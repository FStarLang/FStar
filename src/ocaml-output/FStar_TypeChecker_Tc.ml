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
          let uu____52 = FStar_Ident.string_of_lid lid in
          FStar_Util.smap_try_find tbl uu____52 in
        if FStar_Util.is_some n_opt
        then FStar_All.pipe_right n_opt FStar_Util.must
        else Prims.int_zero in
      let uu____66 = FStar_Options.reuse_hint_for () in
      match uu____66 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____74 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix uu____74 l in
          let uu___15_75 = env in
          let uu____76 =
            let uu____91 =
              let uu____99 = let uu____105 = get_n lid in (lid, uu____105) in
              FStar_Pervasives_Native.Some uu____99 in
            (tbl, uu____91) in
          {
            FStar_TypeChecker_Env.solver =
              (uu___15_75.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___15_75.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___15_75.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___15_75.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___15_75.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___15_75.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___15_75.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___15_75.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___15_75.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___15_75.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___15_75.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___15_75.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___15_75.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___15_75.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___15_75.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___15_75.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___15_75.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___15_75.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___15_75.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___15_75.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___15_75.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___15_75.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___15_75.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___15_75.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___15_75.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___15_75.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___15_75.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___15_75.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___15_75.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___15_75.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___15_75.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____76;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___15_75.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___15_75.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___15_75.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___15_75.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___15_75.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___15_75.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___15_75.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___15_75.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___15_75.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___15_75.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___15_75.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___15_75.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___15_75.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___15_75.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___15_75.FStar_TypeChecker_Env.enable_defer_to_tac)
          }
      | FStar_Pervasives_Native.None ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let uu____128 = FStar_TypeChecker_Env.current_module env in
                let uu____129 =
                  let uu____131 = FStar_Ident.next_id () in
                  FStar_All.pipe_right uu____131 FStar_Util.string_of_int in
                FStar_Ident.lid_add_suffix uu____128 uu____129
            | l::uu____136 -> l in
          let uu___24_139 = env in
          let uu____140 =
            let uu____155 =
              let uu____163 = let uu____169 = get_n lid in (lid, uu____169) in
              FStar_Pervasives_Native.Some uu____163 in
            (tbl, uu____155) in
          {
            FStar_TypeChecker_Env.solver =
              (uu___24_139.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___24_139.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___24_139.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___24_139.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___24_139.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___24_139.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___24_139.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___24_139.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___24_139.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___24_139.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___24_139.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___24_139.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___24_139.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___24_139.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___24_139.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___24_139.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___24_139.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___24_139.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___24_139.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___24_139.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___24_139.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___24_139.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___24_139.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___24_139.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___24_139.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___24_139.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___24_139.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___24_139.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___24_139.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___24_139.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___24_139.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____140;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___24_139.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___24_139.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___24_139.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___24_139.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___24_139.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___24_139.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___24_139.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___24_139.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___24_139.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___24_139.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___24_139.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___24_139.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___24_139.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___24_139.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___24_139.FStar_TypeChecker_Env.enable_defer_to_tac)
          }
let (log : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env ->
    (FStar_Options.log_types ()) &&
      (let uu____195 =
         let uu____197 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____197 in
       Prims.op_Negation uu____195)
let tc_lex_t :
  'uuuuuu209 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'uuuuuu209 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun lids ->
          let err_range =
            let uu____244 = FStar_List.hd ses in
            uu____244.FStar_Syntax_Syntax.sigrng in
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
           | uu____249 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t, uu____255, [], t, uu____257, uu____258);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____260;
               FStar_Syntax_Syntax.sigattrs = uu____261;
               FStar_Syntax_Syntax.sigopts = uu____262;_}::{
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               FStar_Syntax_Syntax.Sig_datacon
                                                               (lex_top,
                                                                uu____264,
                                                                _t_top,
                                                                _lex_t_top,
                                                                uu____302,
                                                                uu____267);
                                                             FStar_Syntax_Syntax.sigrng
                                                               = r1;
                                                             FStar_Syntax_Syntax.sigquals
                                                               = [];
                                                             FStar_Syntax_Syntax.sigmeta
                                                               = uu____269;
                                                             FStar_Syntax_Syntax.sigattrs
                                                               = uu____270;
                                                             FStar_Syntax_Syntax.sigopts
                                                               = uu____271;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons, uu____273, _t_cons, _lex_t_cons, uu____312,
                    uu____276);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____278;
                 FStar_Syntax_Syntax.sigattrs = uu____279;
                 FStar_Syntax_Syntax.sigopts = uu____280;_}::[]
               when
               ((uu____302 = Prims.int_zero) && (uu____312 = Prims.int_zero))
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
                 let uu____339 =
                   let uu____340 =
                     let uu____347 =
                       let uu____350 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.lex_t_lid r1 in
                       FStar_Syntax_Syntax.fvar uu____350
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None in
                     (uu____347, [FStar_Syntax_Syntax.U_name utop]) in
                   FStar_Syntax_Syntax.Tm_uinst uu____340 in
                 FStar_Syntax_Syntax.mk uu____339 r1 in
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
                   let uu____365 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1)) r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____365 in
                 let hd =
                   let uu____367 = FStar_Syntax_Syntax.bv_to_name a in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____367 in
                 let tl =
                   let uu____369 =
                     let uu____370 =
                       let uu____371 =
                         let uu____378 =
                           let uu____381 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2 in
                           FStar_Syntax_Syntax.fvar uu____381
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____378, [FStar_Syntax_Syntax.U_name ucons2]) in
                       FStar_Syntax_Syntax.Tm_uinst uu____371 in
                     FStar_Syntax_Syntax.mk uu____370 r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____369 in
                 let res =
                   let uu____387 =
                     let uu____388 =
                       let uu____395 =
                         let uu____398 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r2 in
                         FStar_Syntax_Syntax.fvar uu____398
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None in
                       (uu____395,
                         [FStar_Syntax_Syntax.U_max
                            [FStar_Syntax_Syntax.U_name ucons1;
                            FStar_Syntax_Syntax.U_name ucons2]]) in
                     FStar_Syntax_Syntax.Tm_uinst uu____388 in
                   FStar_Syntax_Syntax.mk uu____387 r2 in
                 let uu____401 = FStar_Syntax_Syntax.mk_Total res in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd, FStar_Pervasives_Native.None);
                   (tl, FStar_Pervasives_Native.None)] uu____401 in
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
               let uu____440 = FStar_TypeChecker_Env.get_range env in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____440;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = [];
                 FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
               }
           | uu____445 ->
               let err_msg =
                 let uu____450 =
                   let uu____452 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                   FStar_Syntax_Print.sigelt_to_string uu____452 in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____450 in
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
    fun uu____477 ->
      fun expected_typ ->
        fun r ->
          match uu____477 with
          | (uvs, t) ->
              let uu____490 = FStar_Syntax_Subst.open_univ_vars uvs t in
              (match uu____490 with
               | (uvs1, t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                   let t2 =
                     FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t1
                       expected_typ in
                   if uvs1 = []
                   then
                     let uu____502 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2 in
                     (match uu____502 with
                      | (uvs2, t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____520 =
                        let uu____523 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1) in
                        FStar_All.pipe_right uu____523
                          (FStar_Syntax_Subst.close_univ_vars uvs1) in
                      (uvs1, uu____520)))
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun ts ->
      fun r ->
        let uu____546 =
          let uu____547 = FStar_Syntax_Util.type_u () in
          FStar_All.pipe_right uu____547 FStar_Pervasives_Native.fst in
        tc_type_common env ts uu____546 r
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun ts ->
      fun r ->
        let uu____572 =
          let uu____573 = FStar_Syntax_Util.type_u () in
          FStar_All.pipe_right uu____573 FStar_Pervasives_Native.fst in
        tc_type_common env ts uu____572 r
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
            (let uu____631 =
               FStar_TypeChecker_Env.debug env FStar_Options.Low in
             if uu____631
             then
               let uu____634 =
                 FStar_Common.string_of_list
                   FStar_Syntax_Print.sigelt_to_string ses in
               FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____634
             else ());
            (let uu____639 =
               FStar_TypeChecker_TcInductive.check_inductive_well_typedness
                 env ses quals lids in
             match uu____639 with
             | (sig_bndle, tcs, datas) ->
                 let attrs' =
                   FStar_Syntax_Util.remove_attr
                     FStar_Parser_Const.erasable_attr attrs in
                 let data_ops_ses =
                   let uu____673 =
                     FStar_List.map
                       (FStar_TypeChecker_TcInductive.mk_data_operations
                          quals attrs' env tcs) datas in
                   FStar_All.pipe_right uu____673 FStar_List.flatten in
                 ((let uu____687 =
                     (FStar_Options.no_positivity ()) ||
                       (let uu____690 =
                          FStar_TypeChecker_Env.should_verify env in
                        Prims.op_Negation uu____690) in
                   if uu____687
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
                             let uu____707 =
                               match ty.FStar_Syntax_Syntax.sigel with
                               | FStar_Syntax_Syntax.Sig_inductive_typ
                                   (lid, uu____717, uu____718, uu____719,
                                    uu____720, uu____721)
                                   -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                               | uu____730 -> failwith "Impossible!" in
                             match uu____707 with
                             | (lid, r) ->
                                 let uu____738 =
                                   let uu____744 =
                                     let uu____746 =
                                       let uu____748 =
                                         FStar_Ident.string_of_lid lid in
                                       Prims.op_Hat uu____748
                                         " does not satisfy the positivity condition" in
                                     Prims.op_Hat "Inductive type " uu____746 in
                                   (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                     uu____744) in
                                 FStar_Errors.log_issue r uu____738
                           else ()) tcs;
                      FStar_List.iter
                        (fun d ->
                           let uu____762 =
                             match d.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (data_lid, uu____772, uu____773, ty_lid,
                                  uu____775, uu____776)
                                 -> (data_lid, ty_lid)
                             | uu____783 -> failwith "Impossible" in
                           match uu____762 with
                           | (data_lid, ty_lid) ->
                               let uu____791 =
                                 (FStar_Ident.lid_equals ty_lid
                                    FStar_Parser_Const.exn_lid)
                                   &&
                                   (let uu____794 =
                                      FStar_TypeChecker_TcInductive.check_exn_positivity
                                        data_lid env1 in
                                    Prims.op_Negation uu____794) in
                               if uu____791
                               then
                                 let uu____797 =
                                   let uu____803 =
                                     let uu____805 =
                                       let uu____807 =
                                         FStar_Ident.string_of_lid data_lid in
                                       Prims.op_Hat uu____807
                                         " does not satisfy the positivity condition" in
                                     Prims.op_Hat "Exception " uu____805 in
                                   (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                     uu____803) in
                                 FStar_Errors.log_issue
                                   d.FStar_Syntax_Syntax.sigrng uu____797
                               else ()) datas));
                  (let skip_haseq =
                     let skip_prims_type uu____822 =
                       let lid =
                         let ty = FStar_List.hd tcs in
                         match ty.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_inductive_typ
                             (lid, uu____827, uu____828, uu____829,
                              uu____830, uu____831)
                             -> lid
                         | uu____840 -> failwith "Impossible" in
                       FStar_List.existsb
                         (fun s ->
                            let uu____847 =
                              let uu____849 = FStar_Ident.ident_of_lid lid in
                              FStar_Ident.string_of_id uu____849 in
                            s = uu____847)
                         FStar_TypeChecker_TcInductive.early_prims_inductives in
                     let is_noeq =
                       FStar_List.existsb
                         (fun q -> q = FStar_Syntax_Syntax.Noeq) quals in
                     let is_erasable uu____861 =
                       let uu____862 =
                         let uu____865 = FStar_List.hd tcs in
                         uu____865.FStar_Syntax_Syntax.sigattrs in
                       FStar_Syntax_Util.has_attribute uu____862
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
            let pop uu____955 =
              let uu____956 = FStar_TypeChecker_Env.pop env1 "tc_inductive" in
              () in
            try
              (fun uu___203_966 ->
                 match () with
                 | () ->
                     let uu____973 = tc_inductive' env1 ses quals attrs lids in
                     FStar_All.pipe_right uu____973 (fun r -> pop (); r)) ()
            with | uu___202_1004 -> (pop (); FStar_Exn.raise uu___202_1004)
let (check_must_erase_attribute :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let (lbs, l) ->
          let uu____1035 =
            let uu____1037 = FStar_Options.ide () in
            Prims.op_Negation uu____1037 in
          if uu____1035
          then
            let uu____1040 =
              let uu____1045 = FStar_TypeChecker_Env.dsenv env in
              let uu____1046 = FStar_TypeChecker_Env.current_module env in
              FStar_Syntax_DsEnv.iface_decls uu____1045 uu____1046 in
            (match uu____1040 with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some iface_decls ->
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.iter
                      (fun lb ->
                         let lbname =
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                         let has_iface_val =
                           let uu____1070 =
                             let uu____1078 =
                               let uu____1084 =
                                 FStar_Ident.ident_of_lid
                                   (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               FStar_Parser_AST.decl_is_val uu____1084 in
                             FStar_Util.for_some uu____1078 in
                           FStar_All.pipe_right iface_decls uu____1070 in
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
                              let uu____1094 =
                                FStar_Syntax_Syntax.range_of_fv lbname in
                              let uu____1095 =
                                let uu____1101 =
                                  let uu____1103 =
                                    FStar_Syntax_Print.fv_to_string lbname in
                                  let uu____1105 =
                                    FStar_Syntax_Print.fv_to_string lbname in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____1103 uu____1105 in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____1101) in
                              FStar_Errors.log_issue uu____1094 uu____1095
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____1112 =
                                   FStar_Syntax_Syntax.range_of_fv lbname in
                                 let uu____1113 =
                                   let uu____1119 =
                                     let uu____1121 =
                                       FStar_Syntax_Print.fv_to_string lbname in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____1121 in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____1119) in
                                 FStar_Errors.log_issue uu____1112 uu____1113)
                              else ())
                         else ())))
          else ()
      | uu____1131 -> ()
let (unembed_optionstate_knot :
  FStar_Options.optionstate FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let (unembed_optionstate :
  FStar_Syntax_Syntax.term ->
    FStar_Options.optionstate FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____1161 =
      let uu____1168 =
        let uu____1171 = FStar_ST.op_Bang unembed_optionstate_knot in
        FStar_Util.must uu____1171 in
      FStar_Syntax_Embeddings.unembed uu____1168 t in
    uu____1161 true FStar_Syntax_Embeddings.id_norm_cb
let proc_check_with :
  'a . FStar_Syntax_Syntax.attribute Prims.list -> (unit -> 'a) -> 'a =
  fun attrs ->
    fun kont ->
      let uu____1233 =
        FStar_Syntax_Util.get_attribute FStar_Parser_Const.check_with_lid
          attrs in
      match uu____1233 with
      | FStar_Pervasives_Native.None -> kont ()
      | FStar_Pervasives_Native.Some ((a1, FStar_Pervasives_Native.None)::[])
          ->
          FStar_Options.with_saved_options
            (fun uu____1261 ->
               (let uu____1263 =
                  let uu____1264 = unembed_optionstate a1 in
                  FStar_All.pipe_right uu____1264 FStar_Util.must in
                FStar_Options.set uu____1263);
               kont ())
      | uu____1269 -> failwith "huh?"
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
        (fun uu____1381 ->
           let r = se.FStar_Syntax_Syntax.sigrng in
           let se1 =
             let uu____1384 = FStar_Options.record_options () in
             if uu____1384
             then
               let uu___250_1387 = se in
               let uu____1388 =
                 let uu____1391 = FStar_Options.peek () in
                 FStar_Pervasives_Native.Some uu____1391 in
               {
                 FStar_Syntax_Syntax.sigel =
                   (uu___250_1387.FStar_Syntax_Syntax.sigel);
                 FStar_Syntax_Syntax.sigrng =
                   (uu___250_1387.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___250_1387.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___250_1387.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___250_1387.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts = uu____1388
               }
             else se in
           match se1.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ uu____1404 ->
               failwith "Impossible bare data-constructor"
           | FStar_Syntax_Syntax.Sig_datacon uu____1432 ->
               failwith "Impossible bare data-constructor"
           | FStar_Syntax_Syntax.Sig_fail (uu____1459, false, uu____1460)
               when
               (let uu____1475 = FStar_TypeChecker_Env.should_verify env in
                Prims.op_Negation uu____1475) ||
                 (FStar_Options.admit_smt_queries ())
               -> ([], [], env)
           | FStar_Syntax_Syntax.Sig_fail (expected_errors, lax, ses) ->
               let env' =
                 if lax
                 then
                   let uu___268_1498 = env in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___268_1498.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___268_1498.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___268_1498.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___268_1498.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___268_1498.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___268_1498.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___268_1498.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___268_1498.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___268_1498.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___268_1498.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___268_1498.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___268_1498.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___268_1498.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___268_1498.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___268_1498.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___268_1498.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___268_1498.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.use_eq_strict =
                       (uu___268_1498.FStar_TypeChecker_Env.use_eq_strict);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___268_1498.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___268_1498.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___268_1498.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___268_1498.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___268_1498.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___268_1498.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___268_1498.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___268_1498.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___268_1498.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___268_1498.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___268_1498.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___268_1498.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___268_1498.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___268_1498.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___268_1498.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___268_1498.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___268_1498.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.try_solve_implicits_hook =
                       (uu___268_1498.FStar_TypeChecker_Env.try_solve_implicits_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___268_1498.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.mpreprocess =
                       (uu___268_1498.FStar_TypeChecker_Env.mpreprocess);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___268_1498.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___268_1498.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___268_1498.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___268_1498.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___268_1498.FStar_TypeChecker_Env.nbe);
                     FStar_TypeChecker_Env.strict_args_tab =
                       (uu___268_1498.FStar_TypeChecker_Env.strict_args_tab);
                     FStar_TypeChecker_Env.erasable_types_tab =
                       (uu___268_1498.FStar_TypeChecker_Env.erasable_types_tab);
                     FStar_TypeChecker_Env.enable_defer_to_tac =
                       (uu___268_1498.FStar_TypeChecker_Env.enable_defer_to_tac)
                   }
                 else env in
               let env'1 = FStar_TypeChecker_Env.push env' "expect_failure" in
               ((let uu____1505 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Low in
                 if uu____1505
                 then
                   let uu____1508 =
                     let uu____1510 =
                       FStar_List.map FStar_Util.string_of_int
                         expected_errors in
                     FStar_All.pipe_left (FStar_String.concat "; ")
                       uu____1510 in
                   FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____1508
                 else ());
                (let uu____1524 =
                   FStar_Errors.catch_errors
                     (fun uu____1554 ->
                        FStar_Options.with_saved_options
                          (fun uu____1567 ->
                             let uu____1568 =
                               let uu____1589 =
                                 FStar_ST.op_Bang tc_decls_knot in
                               FStar_Util.must uu____1589 in
                             uu____1568 env'1 ses)) in
                 match uu____1524 with
                 | (errs, uu____1698) ->
                     ((let uu____1728 =
                         (FStar_Options.print_expected_failures ()) ||
                           (FStar_TypeChecker_Env.debug env FStar_Options.Low) in
                       if uu____1728
                       then
                         (FStar_Util.print_string ">> Got issues: [\n";
                          FStar_List.iter FStar_Errors.print_issue errs;
                          FStar_Util.print_string ">>]\n")
                       else ());
                      (let uu____1737 =
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
                        | uu____1751 ->
                            if expected_errors <> []
                            then
                              let uu____1759 =
                                FStar_Errors.find_multiset_discrepancy
                                  expected_errors actual_errors in
                              (match uu____1759 with
                               | FStar_Pervasives_Native.None -> ()
                               | FStar_Pervasives_Native.Some (e, n1, n2) ->
                                   (FStar_List.iter FStar_Errors.print_issue
                                      errs;
                                    (let uu____1799 =
                                       let uu____1805 =
                                         let uu____1807 =
                                           FStar_Common.string_of_list
                                             FStar_Util.string_of_int
                                             expected_errors in
                                         let uu____1810 =
                                           FStar_Common.string_of_list
                                             FStar_Util.string_of_int
                                             actual_errors in
                                         let uu____1813 =
                                           FStar_Util.string_of_int e in
                                         let uu____1815 =
                                           FStar_Util.string_of_int n2 in
                                         let uu____1817 =
                                           FStar_Util.string_of_int n1 in
                                         FStar_Util.format5
                                           "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                           uu____1807 uu____1810 uu____1813
                                           uu____1815 uu____1817 in
                                       (FStar_Errors.Error_DidNotFail,
                                         uu____1805) in
                                     FStar_Errors.log_issue
                                       se1.FStar_Syntax_Syntax.sigrng
                                       uu____1799)))
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
                 let uu____1860 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env1) in
                 if uu____1860
                 then
                   let ses1 =
                     let uu____1868 =
                       let uu____1869 =
                         let uu____1870 =
                           tc_inductive
                             (let uu___310_1879 = env1 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___310_1879.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___310_1879.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___310_1879.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___310_1879.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___310_1879.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___310_1879.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___310_1879.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___310_1879.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___310_1879.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___310_1879.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___310_1879.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___310_1879.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___310_1879.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___310_1879.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___310_1879.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___310_1879.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___310_1879.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (uu___310_1879.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___310_1879.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___310_1879.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___310_1879.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___310_1879.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___310_1879.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___310_1879.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___310_1879.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___310_1879.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___310_1879.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___310_1879.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___310_1879.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___310_1879.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___310_1879.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___310_1879.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___310_1879.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___310_1879.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___310_1879.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___310_1879.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (uu___310_1879.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___310_1879.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___310_1879.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___310_1879.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___310_1879.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___310_1879.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___310_1879.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___310_1879.FStar_TypeChecker_Env.erasable_types_tab);
                                FStar_TypeChecker_Env.enable_defer_to_tac =
                                  (uu___310_1879.FStar_TypeChecker_Env.enable_defer_to_tac)
                              }) ses se1.FStar_Syntax_Syntax.sigquals
                             se1.FStar_Syntax_Syntax.sigattrs lids in
                         FStar_All.pipe_right uu____1870
                           FStar_Pervasives_Native.fst in
                       FStar_All.pipe_right uu____1869
                         (FStar_TypeChecker_Normalize.elim_uvars env1) in
                     FStar_All.pipe_right uu____1868
                       FStar_Syntax_Util.ses_of_sigbundle in
                   ((let uu____1893 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases") in
                     if uu____1893
                     then
                       let uu____1898 =
                         FStar_Syntax_Print.sigelt_to_string
                           (let uu___314_1902 = se1 in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                              FStar_Syntax_Syntax.sigrng =
                                (uu___314_1902.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___314_1902.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___314_1902.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___314_1902.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (uu___314_1902.FStar_Syntax_Syntax.sigopts)
                            }) in
                       FStar_Util.print1 "Inductive after phase 1: %s\n"
                         uu____1898
                     else ());
                    ses1)
                 else ses in
               let uu____1912 =
                 tc_inductive env1 ses1 se1.FStar_Syntax_Syntax.sigquals
                   se1.FStar_Syntax_Syntax.sigattrs lids in
               (match uu____1912 with
                | (sigbndle, projectors_ses) ->
                    let sigbndle1 =
                      let uu___321_1936 = sigbndle in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___321_1936.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___321_1936.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___321_1936.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___321_1936.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (se1.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___321_1936.FStar_Syntax_Syntax.sigopts)
                      } in
                    ([sigbndle1], projectors_ses, env0))
           | FStar_Syntax_Syntax.Sig_pragma p ->
               (FStar_Syntax_Util.process_pragma p r; ([se1], [], env0))
           | FStar_Syntax_Syntax.Sig_new_effect ne ->
               let is_unelaborated_dm4f =
                 match ne.FStar_Syntax_Syntax.combinators with
                 | FStar_Syntax_Syntax.DM4F_eff combs ->
                     let uu____1952 =
                       let uu____1955 =
                         FStar_All.pipe_right
                           combs.FStar_Syntax_Syntax.ret_wp
                           FStar_Pervasives_Native.snd in
                       FStar_All.pipe_right uu____1955
                         FStar_Syntax_Subst.compress in
                     (match uu____1952 with
                      | {
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_unknown;
                          FStar_Syntax_Syntax.pos = uu____1971;
                          FStar_Syntax_Syntax.vars = uu____1972;_} -> true
                      | uu____1976 -> false)
                 | uu____1980 -> false in
               if is_unelaborated_dm4f
               then
                 let env1 = FStar_TypeChecker_Env.set_range env r in
                 let uu____1994 =
                   FStar_TypeChecker_TcEffect.dmff_cps_and_elaborate env1 ne in
                 (match uu____1994 with
                  | (ses, ne1, lift_from_pure_opt) ->
                      let effect_and_lift_ses =
                        match lift_from_pure_opt with
                        | FStar_Pervasives_Native.Some lift ->
                            [(let uu___346_2033 = se1 in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___346_2033.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___346_2033.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___346_2033.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___346_2033.FStar_Syntax_Syntax.sigattrs);
                                FStar_Syntax_Syntax.sigopts =
                                  (uu___346_2033.FStar_Syntax_Syntax.sigopts)
                              });
                            lift]
                        | FStar_Pervasives_Native.None ->
                            [(let uu___349_2035 = se1 in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___349_2035.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___349_2035.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___349_2035.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___349_2035.FStar_Syntax_Syntax.sigattrs);
                                FStar_Syntax_Syntax.sigopts =
                                  (uu___349_2035.FStar_Syntax_Syntax.sigopts)
                              })] in
                      ([], (FStar_List.append ses effect_and_lift_ses), env0))
               else
                 (let ne1 =
                    let uu____2043 =
                      (FStar_Options.use_two_phase_tc ()) &&
                        (FStar_TypeChecker_Env.should_verify env) in
                    if uu____2043
                    then
                      let ne1 =
                        let uu____2047 =
                          let uu____2048 =
                            let uu____2049 =
                              FStar_TypeChecker_TcEffect.tc_eff_decl
                                (let uu___353_2052 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___353_2052.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___353_2052.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___353_2052.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___353_2052.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___353_2052.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___353_2052.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___353_2052.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___353_2052.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___353_2052.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___353_2052.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___353_2052.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___353_2052.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___353_2052.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___353_2052.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___353_2052.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___353_2052.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___353_2052.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___353_2052.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___353_2052.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___353_2052.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___353_2052.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 = true;
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___353_2052.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___353_2052.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___353_2052.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___353_2052.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___353_2052.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___353_2052.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___353_2052.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___353_2052.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___353_2052.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___353_2052.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___353_2052.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___353_2052.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___353_2052.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___353_2052.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___353_2052.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___353_2052.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___353_2052.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___353_2052.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___353_2052.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___353_2052.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___353_2052.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___353_2052.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___353_2052.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___353_2052.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 }) ne se1.FStar_Syntax_Syntax.sigquals in
                            FStar_All.pipe_right uu____2049
                              (fun ne1 ->
                                 let uu___356_2058 = se1 in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___356_2058.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals =
                                     (uu___356_2058.FStar_Syntax_Syntax.sigquals);
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___356_2058.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___356_2058.FStar_Syntax_Syntax.sigattrs);
                                   FStar_Syntax_Syntax.sigopts =
                                     (uu___356_2058.FStar_Syntax_Syntax.sigopts)
                                 }) in
                          FStar_All.pipe_right uu____2048
                            (FStar_TypeChecker_Normalize.elim_uvars env) in
                        FStar_All.pipe_right uu____2047
                          FStar_Syntax_Util.eff_decl_of_new_effect in
                      ((let uu____2060 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "TwoPhases") in
                        if uu____2060
                        then
                          let uu____2065 =
                            FStar_Syntax_Print.sigelt_to_string
                              (let uu___360_2069 = se1 in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___360_2069.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals =
                                   (uu___360_2069.FStar_Syntax_Syntax.sigquals);
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___360_2069.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___360_2069.FStar_Syntax_Syntax.sigattrs);
                                 FStar_Syntax_Syntax.sigopts =
                                   (uu___360_2069.FStar_Syntax_Syntax.sigopts)
                               }) in
                          FStar_Util.print1 "Effect decl after phase 1: %s\n"
                            uu____2065
                        else ());
                       ne1)
                    else ne in
                  let ne2 =
                    FStar_TypeChecker_TcEffect.tc_eff_decl env ne1
                      se1.FStar_Syntax_Syntax.sigquals in
                  let se2 =
                    let uu___365_2077 = se1 in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_new_effect ne2);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___365_2077.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___365_2077.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___365_2077.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___365_2077.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___365_2077.FStar_Syntax_Syntax.sigopts)
                    } in
                  ([se2], [], env0))
           | FStar_Syntax_Syntax.Sig_sub_effect sub ->
               let sub1 = FStar_TypeChecker_TcEffect.tc_lift env sub r in
               let se2 =
                 let uu___371_2085 = se1 in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_sub_effect sub1);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___371_2085.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___371_2085.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___371_2085.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___371_2085.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (uu___371_2085.FStar_Syntax_Syntax.sigopts)
                 } in
               ([se2], [], env)
           | FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, flags)
               ->
               let uu____2099 =
                 let uu____2108 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env) in
                 if uu____2108
                 then
                   let uu____2119 =
                     let uu____2120 =
                       let uu____2121 =
                         FStar_TypeChecker_TcEffect.tc_effect_abbrev
                           (let uu___382_2132 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___382_2132.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___382_2132.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___382_2132.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___382_2132.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___382_2132.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___382_2132.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___382_2132.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___382_2132.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___382_2132.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___382_2132.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___382_2132.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___382_2132.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___382_2132.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___382_2132.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___382_2132.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___382_2132.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___382_2132.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___382_2132.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___382_2132.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___382_2132.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___382_2132.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 = true;
                              FStar_TypeChecker_Env.failhard =
                                (uu___382_2132.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___382_2132.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___382_2132.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___382_2132.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___382_2132.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___382_2132.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___382_2132.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___382_2132.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___382_2132.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___382_2132.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___382_2132.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___382_2132.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___382_2132.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___382_2132.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___382_2132.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___382_2132.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___382_2132.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___382_2132.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___382_2132.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___382_2132.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___382_2132.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___382_2132.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___382_2132.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___382_2132.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) (lid, uvs, tps, c) r in
                       FStar_All.pipe_right uu____2121
                         (fun uu____2149 ->
                            match uu____2149 with
                            | (lid1, uvs1, tps1, c1) ->
                                let uu___389_2162 = se1 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_effect_abbrev
                                       (lid1, uvs1, tps1, c1, flags));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___389_2162.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___389_2162.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___389_2162.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___389_2162.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___389_2162.FStar_Syntax_Syntax.sigopts)
                                }) in
                     FStar_All.pipe_right uu____2120
                       (FStar_TypeChecker_Normalize.elim_uvars env) in
                   FStar_All.pipe_right uu____2119
                     (fun se2 ->
                        match se2.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_effect_abbrev
                            (lid1, uvs1, tps1, c1, uu____2192) ->
                            (lid1, uvs1, tps1, c1)
                        | uu____2197 ->
                            failwith
                              "Did not expect Sig_effect_abbrev to not be one after phase 1")
                 else (lid, uvs, tps, c) in
               (match uu____2099 with
                | (lid1, uvs1, tps1, c1) ->
                    let uu____2223 =
                      FStar_TypeChecker_TcEffect.tc_effect_abbrev env
                        (lid1, uvs1, tps1, c1) r in
                    (match uu____2223 with
                     | (lid2, uvs2, tps2, c2) ->
                         let se2 =
                           let uu___410_2247 = se1 in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  (lid2, uvs2, tps2, c2, flags));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___410_2247.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___410_2247.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___410_2247.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___410_2247.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___410_2247.FStar_Syntax_Syntax.sigopts)
                           } in
                         ([se2], [], env0)))
           | FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2254, uu____2255, uu____2256) when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___0_2261 ->
                       match uu___0_2261 with
                       | FStar_Syntax_Syntax.OnlyName -> true
                       | uu____2264 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_let (uu____2270, uu____2271) when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___0_2280 ->
                       match uu___0_2280 with
                       | FStar_Syntax_Syntax.OnlyName -> true
                       | uu____2283 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) ->
               let env1 = FStar_TypeChecker_Env.set_range env r in
               ((let uu____2294 = FStar_TypeChecker_Env.lid_exists env1 lid in
                 if uu____2294
                 then
                   let uu____2297 =
                     let uu____2303 =
                       let uu____2305 = FStar_Ident.string_of_lid lid in
                       FStar_Util.format1
                         "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                         uu____2305 in
                     (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                       uu____2303) in
                   FStar_Errors.raise_error uu____2297 r
                 else ());
                (let uu____2311 =
                   let uu____2320 =
                     (FStar_Options.use_two_phase_tc ()) &&
                       (FStar_TypeChecker_Env.should_verify env1) in
                   if uu____2320
                   then
                     let uu____2331 =
                       tc_declare_typ
                         (let uu___434_2334 = env1 in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___434_2334.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___434_2334.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___434_2334.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___434_2334.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___434_2334.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___434_2334.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___434_2334.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___434_2334.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___434_2334.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___434_2334.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___434_2334.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___434_2334.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___434_2334.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___434_2334.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___434_2334.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___434_2334.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___434_2334.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___434_2334.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___434_2334.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___434_2334.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___434_2334.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___434_2334.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___434_2334.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___434_2334.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___434_2334.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___434_2334.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___434_2334.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___434_2334.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___434_2334.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___434_2334.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___434_2334.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___434_2334.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___434_2334.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___434_2334.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___434_2334.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___434_2334.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___434_2334.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___434_2334.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___434_2334.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___434_2334.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___434_2334.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___434_2334.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___434_2334.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___434_2334.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___434_2334.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng in
                     match uu____2331 with
                     | (uvs1, t1) ->
                         ((let uu____2360 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "TwoPhases") in
                           if uu____2360
                           then
                             let uu____2365 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____2367 =
                               FStar_Syntax_Print.univ_names_to_string uvs1 in
                             FStar_Util.print2
                               "Val declaration after phase 1: %s and uvs: %s\n"
                               uu____2365 uu____2367
                           else ());
                          (uvs1, t1))
                   else (uvs, t) in
                 match uu____2311 with
                 | (uvs1, t1) ->
                     let uu____2402 =
                       tc_declare_typ env1 (uvs1, t1)
                         se1.FStar_Syntax_Syntax.sigrng in
                     (match uu____2402 with
                      | (uvs2, t2) ->
                          ([(let uu___447_2432 = se1 in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (lid, uvs2, t2));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___447_2432.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___447_2432.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___447_2432.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___447_2432.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___447_2432.FStar_Syntax_Syntax.sigopts)
                             })], [], env0))))
           | FStar_Syntax_Syntax.Sig_assume (lid, uvs, t) ->
               ((let uu____2437 =
                   let uu____2443 =
                     let uu____2445 = FStar_Syntax_Print.lid_to_string lid in
                     FStar_Util.format1 "Admitting a top-level assumption %s"
                       uu____2445 in
                   (FStar_Errors.Warning_WarnOnUse, uu____2443) in
                 FStar_Errors.log_issue r uu____2437);
                (let env1 = FStar_TypeChecker_Env.set_range env r in
                 let uu____2450 =
                   let uu____2459 =
                     (FStar_Options.use_two_phase_tc ()) &&
                       (FStar_TypeChecker_Env.should_verify env1) in
                   if uu____2459
                   then
                     let uu____2470 =
                       tc_assume
                         (let uu___457_2473 = env1 in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___457_2473.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___457_2473.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___457_2473.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___457_2473.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___457_2473.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___457_2473.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___457_2473.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___457_2473.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___457_2473.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___457_2473.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___457_2473.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___457_2473.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___457_2473.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___457_2473.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___457_2473.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___457_2473.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___457_2473.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___457_2473.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___457_2473.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___457_2473.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___457_2473.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___457_2473.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___457_2473.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___457_2473.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___457_2473.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___457_2473.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___457_2473.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___457_2473.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___457_2473.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___457_2473.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___457_2473.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___457_2473.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___457_2473.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___457_2473.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___457_2473.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___457_2473.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___457_2473.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___457_2473.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___457_2473.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___457_2473.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___457_2473.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___457_2473.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___457_2473.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___457_2473.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___457_2473.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng in
                     match uu____2470 with
                     | (uvs1, t1) ->
                         ((let uu____2499 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "TwoPhases") in
                           if uu____2499
                           then
                             let uu____2504 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____2506 =
                               FStar_Syntax_Print.univ_names_to_string uvs1 in
                             FStar_Util.print2
                               "Assume after phase 1: %s and uvs: %s\n"
                               uu____2504 uu____2506
                           else ());
                          (uvs1, t1))
                   else (uvs, t) in
                 match uu____2450 with
                 | (uvs1, t1) ->
                     let uu____2541 =
                       tc_assume env1 (uvs1, t1)
                         se1.FStar_Syntax_Syntax.sigrng in
                     (match uu____2541 with
                      | (uvs2, t2) ->
                          ([(let uu___470_2571 = se1 in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_assume
                                    (lid, uvs2, t2));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___470_2571.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___470_2571.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___470_2571.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___470_2571.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___470_2571.FStar_Syntax_Syntax.sigopts)
                             })], [], env0))))
           | FStar_Syntax_Syntax.Sig_splice (lids, t) ->
               ((let uu____2579 = FStar_Options.debug_any () in
                 if uu____2579
                 then
                   let uu____2582 =
                     FStar_Ident.string_of_lid
                       env.FStar_TypeChecker_Env.curmodule in
                   let uu____2584 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print2 "%s: Found splice of (%s)\n" uu____2582
                     uu____2584
                 else ());
                (let uu____2589 =
                   FStar_TypeChecker_TcTerm.tc_tactic
                     FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_decls
                     env t in
                 match uu____2589 with
                 | (t1, uu____2607, g) ->
                     (FStar_TypeChecker_Rel.force_trivial_guard env g;
                      (let ses =
                         env.FStar_TypeChecker_Env.splice env
                           se1.FStar_Syntax_Syntax.sigrng t1 in
                       let lids' =
                         FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                           ses in
                       FStar_List.iter
                         (fun lid ->
                            let uu____2621 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids' in
                            match uu____2621 with
                            | FStar_Pervasives_Native.None when
                                Prims.op_Negation
                                  env.FStar_TypeChecker_Env.nosynth
                                ->
                                let uu____2624 =
                                  let uu____2630 =
                                    let uu____2632 =
                                      FStar_Ident.string_of_lid lid in
                                    let uu____2634 =
                                      let uu____2636 =
                                        FStar_List.map
                                          FStar_Ident.string_of_lid lids' in
                                      FStar_All.pipe_left
                                        (FStar_String.concat ", ") uu____2636 in
                                    FStar_Util.format2
                                      "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                      uu____2632 uu____2634 in
                                  (FStar_Errors.Fatal_SplicedUndef,
                                    uu____2630) in
                                FStar_Errors.raise_error uu____2624 r
                            | uu____2648 -> ()) lids;
                       (let dsenv =
                          FStar_List.fold_left
                            FStar_Syntax_DsEnv.push_sigelt_force
                            env.FStar_TypeChecker_Env.dsenv ses in
                        let env1 =
                          let uu___490_2653 = env in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___490_2653.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___490_2653.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___490_2653.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___490_2653.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___490_2653.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___490_2653.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___490_2653.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___490_2653.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___490_2653.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___490_2653.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___490_2653.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___490_2653.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___490_2653.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___490_2653.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___490_2653.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___490_2653.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___490_2653.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___490_2653.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___490_2653.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___490_2653.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___490_2653.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___490_2653.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___490_2653.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___490_2653.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___490_2653.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___490_2653.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___490_2653.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___490_2653.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___490_2653.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___490_2653.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___490_2653.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___490_2653.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___490_2653.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___490_2653.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___490_2653.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___490_2653.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___490_2653.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___490_2653.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___490_2653.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___490_2653.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___490_2653.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___490_2653.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv = dsenv;
                            FStar_TypeChecker_Env.nbe =
                              (uu___490_2653.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___490_2653.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___490_2653.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___490_2653.FStar_TypeChecker_Env.enable_defer_to_tac)
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
                     let uu____2721 =
                       let uu____2723 =
                         let uu____2732 = drop_logic val_q in
                         let uu____2735 = drop_logic q' in
                         (uu____2732, uu____2735) in
                       match uu____2723 with
                       | (val_q1, q'1) ->
                           ((FStar_List.length val_q1) =
                              (FStar_List.length q'1))
                             &&
                             (FStar_List.forall2
                                FStar_Syntax_Util.qualifier_equal val_q1 q'1) in
                     if uu____2721
                     then FStar_Pervasives_Native.Some q'
                     else
                       (let uu____2762 =
                          let uu____2768 =
                            let uu____2770 =
                              FStar_Syntax_Print.lid_to_string l in
                            let uu____2772 =
                              FStar_Syntax_Print.quals_to_string val_q in
                            let uu____2774 =
                              FStar_Syntax_Print.quals_to_string q' in
                            FStar_Util.format3
                              "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                              uu____2770 uu____2772 uu____2774 in
                          (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                            uu____2768) in
                        FStar_Errors.raise_error uu____2762 r) in
               let rename_parameters lb =
                 let rename_in_typ def typ =
                   let typ1 = FStar_Syntax_Subst.compress typ in
                   let def_bs =
                     let uu____2811 =
                       let uu____2812 = FStar_Syntax_Subst.compress def in
                       uu____2812.FStar_Syntax_Syntax.n in
                     match uu____2811 with
                     | FStar_Syntax_Syntax.Tm_abs
                         (binders, uu____2824, uu____2825) -> binders
                     | uu____2850 -> [] in
                   match typ1 with
                   | {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                         (val_bs, c);
                       FStar_Syntax_Syntax.pos = r1;
                       FStar_Syntax_Syntax.vars = uu____2862;_} ->
                       let has_auto_name bv =
                         let uu____2892 =
                           FStar_Ident.string_of_id
                             bv.FStar_Syntax_Syntax.ppname in
                         FStar_Util.starts_with uu____2892
                           FStar_Ident.reserved_prefix in
                       let rec rename_binders def_bs1 val_bs1 =
                         match (def_bs1, val_bs1) with
                         | ([], uu____2969) -> val_bs1
                         | (uu____3000, []) -> val_bs1
                         | ((body_bv, uu____3032)::bt, (val_bv, aqual)::vt)
                             ->
                             let uu____3089 =
                               let uu____3096 =
                                 let uu____3103 = has_auto_name body_bv in
                                 let uu____3105 = has_auto_name val_bv in
                                 (uu____3103, uu____3105) in
                               match uu____3096 with
                               | (true, uu____3115) -> (val_bv, aqual)
                               | (false, true) ->
                                   let uu____3126 =
                                     let uu___559_3127 = val_bv in
                                     let uu____3128 =
                                       let uu____3129 =
                                         let uu____3135 =
                                           FStar_Ident.string_of_id
                                             body_bv.FStar_Syntax_Syntax.ppname in
                                         let uu____3137 =
                                           FStar_Ident.range_of_id
                                             val_bv.FStar_Syntax_Syntax.ppname in
                                         (uu____3135, uu____3137) in
                                       FStar_Ident.mk_ident uu____3129 in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         uu____3128;
                                       FStar_Syntax_Syntax.index =
                                         (uu___559_3127.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (uu___559_3127.FStar_Syntax_Syntax.sort)
                                     } in
                                   (uu____3126, aqual)
                               | (false, false) -> (val_bv, aqual) in
                             let uu____3147 = rename_binders bt vt in
                             uu____3089 :: uu____3147 in
                       let uu____3162 =
                         let uu____3163 =
                           let uu____3178 = rename_binders def_bs val_bs in
                           (uu____3178, c) in
                         FStar_Syntax_Syntax.Tm_arrow uu____3163 in
                       FStar_Syntax_Syntax.mk uu____3162 r1
                   | uu____3197 -> typ1 in
                 let uu___565_3198 = lb in
                 let uu____3199 =
                   rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                     lb.FStar_Syntax_Syntax.lbtyp in
                 {
                   FStar_Syntax_Syntax.lbname =
                     (uu___565_3198.FStar_Syntax_Syntax.lbname);
                   FStar_Syntax_Syntax.lbunivs =
                     (uu___565_3198.FStar_Syntax_Syntax.lbunivs);
                   FStar_Syntax_Syntax.lbtyp = uu____3199;
                   FStar_Syntax_Syntax.lbeff =
                     (uu___565_3198.FStar_Syntax_Syntax.lbeff);
                   FStar_Syntax_Syntax.lbdef =
                     (uu___565_3198.FStar_Syntax_Syntax.lbdef);
                   FStar_Syntax_Syntax.lbattrs =
                     (uu___565_3198.FStar_Syntax_Syntax.lbattrs);
                   FStar_Syntax_Syntax.lbpos =
                     (uu___565_3198.FStar_Syntax_Syntax.lbpos)
                 } in
               let uu____3202 =
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.fold_left
                      (fun uu____3257 ->
                         fun lb ->
                           match uu____3257 with
                           | (gen, lbs1, quals_opt) ->
                               let lbname =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu____3303 =
                                 let uu____3315 =
                                   FStar_TypeChecker_Env.try_lookup_val_decl
                                     env1
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 match uu____3315 with
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
                                       | uu____3395 ->
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
                                      (let uu____3442 =
                                         FStar_Syntax_Syntax.mk_lb
                                           ((FStar_Util.Inr lbname), uvs,
                                             FStar_Parser_Const.effect_ALL_lid,
                                             tval, def, [],
                                             (lb.FStar_Syntax_Syntax.lbpos)) in
                                       (false, uu____3442, quals_opt1))) in
                               (match uu____3303 with
                                | (gen1, lb1, quals_opt1) ->
                                    (gen1, (lb1 :: lbs1), quals_opt1)))
                      (true, [],
                        (if se1.FStar_Syntax_Syntax.sigquals = []
                         then FStar_Pervasives_Native.None
                         else
                           FStar_Pervasives_Native.Some
                             (se1.FStar_Syntax_Syntax.sigquals)))) in
               (match uu____3202 with
                | (should_generalize, lbs', quals_opt) ->
                    let quals =
                      match quals_opt with
                      | FStar_Pervasives_Native.None ->
                          [FStar_Syntax_Syntax.Visible_default]
                      | FStar_Pervasives_Native.Some q ->
                          let uu____3546 =
                            FStar_All.pipe_right q
                              (FStar_Util.for_some
                                 (fun uu___1_3552 ->
                                    match uu___1_3552 with
                                    | FStar_Syntax_Syntax.Irreducible -> true
                                    | FStar_Syntax_Syntax.Visible_default ->
                                        true
                                    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                        -> true
                                    | uu____3557 -> false)) in
                          if uu____3546
                          then q
                          else FStar_Syntax_Syntax.Visible_default :: q in
                    let lbs'1 = FStar_List.rev lbs' in
                    let uu____3567 =
                      let uu____3576 =
                        FStar_Syntax_Util.extract_attr'
                          FStar_Parser_Const.preprocess_with
                          se1.FStar_Syntax_Syntax.sigattrs in
                      match uu____3576 with
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
                    (match uu____3567 with
                     | (attrs, pre_tau) ->
                         let se2 =
                           let uu___623_3681 = se1 in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___623_3681.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___623_3681.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___623_3681.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___623_3681.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs = attrs;
                             FStar_Syntax_Syntax.sigopts =
                               (uu___623_3681.FStar_Syntax_Syntax.sigopts)
                           } in
                         let preprocess_lb tau lb =
                           let lbdef =
                             FStar_TypeChecker_Env.preprocess env1 tau
                               lb.FStar_Syntax_Syntax.lbdef in
                           (let uu____3695 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TwoPhases") in
                            if uu____3695
                            then
                              let uu____3700 =
                                FStar_Syntax_Print.term_to_string lbdef in
                              FStar_Util.print1 "lb preprocessed into: %s\n"
                                uu____3700
                            else ());
                           (let uu___632_3705 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___632_3705.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___632_3705.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___632_3705.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___632_3705.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___632_3705.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___632_3705.FStar_Syntax_Syntax.lbpos)
                            }) in
                         let lbs'2 =
                           match pre_tau with
                           | FStar_Pervasives_Native.Some tau ->
                               FStar_List.map (preprocess_lb tau) lbs'1
                           | FStar_Pervasives_Native.None -> lbs'1 in
                         let e =
                           let uu____3715 =
                             let uu____3716 =
                               let uu____3730 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_constant
                                      FStar_Const.Const_unit) r in
                               (((FStar_Pervasives_Native.fst lbs), lbs'2),
                                 uu____3730) in
                             FStar_Syntax_Syntax.Tm_let uu____3716 in
                           FStar_Syntax_Syntax.mk uu____3715 r in
                         let env' =
                           let uu___639_3749 = env1 in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___639_3749.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___639_3749.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___639_3749.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___639_3749.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___639_3749.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___639_3749.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___639_3749.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___639_3749.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___639_3749.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___639_3749.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___639_3749.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___639_3749.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               should_generalize;
                             FStar_TypeChecker_Env.letrecs =
                               (uu___639_3749.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = true;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___639_3749.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___639_3749.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___639_3749.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___639_3749.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___639_3749.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___639_3749.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___639_3749.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___639_3749.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___639_3749.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___639_3749.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___639_3749.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___639_3749.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___639_3749.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___639_3749.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___639_3749.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___639_3749.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___639_3749.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___639_3749.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___639_3749.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___639_3749.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___639_3749.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___639_3749.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___639_3749.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___639_3749.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___639_3749.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___639_3749.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___639_3749.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___639_3749.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___639_3749.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___639_3749.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___639_3749.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___639_3749.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let e1 =
                           let uu____3752 =
                             (FStar_Options.use_two_phase_tc ()) &&
                               (FStar_TypeChecker_Env.should_verify env') in
                           if uu____3752
                           then
                             let drop_lbtyp e_lax =
                               let uu____3761 =
                                 let uu____3762 =
                                   FStar_Syntax_Subst.compress e_lax in
                                 uu____3762.FStar_Syntax_Syntax.n in
                               match uu____3761 with
                               | FStar_Syntax_Syntax.Tm_let
                                   ((false, lb::[]), e2) ->
                                   let lb_unannotated =
                                     let uu____3784 =
                                       let uu____3785 =
                                         FStar_Syntax_Subst.compress e in
                                       uu____3785.FStar_Syntax_Syntax.n in
                                     match uu____3784 with
                                     | FStar_Syntax_Syntax.Tm_let
                                         ((uu____3789, lb1::[]), uu____3791)
                                         ->
                                         let uu____3807 =
                                           let uu____3808 =
                                             FStar_Syntax_Subst.compress
                                               lb1.FStar_Syntax_Syntax.lbtyp in
                                           uu____3808.FStar_Syntax_Syntax.n in
                                         (match uu____3807 with
                                          | FStar_Syntax_Syntax.Tm_unknown ->
                                              true
                                          | uu____3813 -> false)
                                     | uu____3815 ->
                                         failwith
                                           "Impossible: first phase lb and second phase lb differ in structure!" in
                                   if lb_unannotated
                                   then
                                     let uu___664_3819 = e_lax in
                                     {
                                       FStar_Syntax_Syntax.n =
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((false,
                                               [(let uu___666_3834 = lb in
                                                 {
                                                   FStar_Syntax_Syntax.lbname
                                                     =
                                                     (uu___666_3834.FStar_Syntax_Syntax.lbname);
                                                   FStar_Syntax_Syntax.lbunivs
                                                     =
                                                     (uu___666_3834.FStar_Syntax_Syntax.lbunivs);
                                                   FStar_Syntax_Syntax.lbtyp
                                                     =
                                                     FStar_Syntax_Syntax.tun;
                                                   FStar_Syntax_Syntax.lbeff
                                                     =
                                                     (uu___666_3834.FStar_Syntax_Syntax.lbeff);
                                                   FStar_Syntax_Syntax.lbdef
                                                     =
                                                     (uu___666_3834.FStar_Syntax_Syntax.lbdef);
                                                   FStar_Syntax_Syntax.lbattrs
                                                     =
                                                     (uu___666_3834.FStar_Syntax_Syntax.lbattrs);
                                                   FStar_Syntax_Syntax.lbpos
                                                     =
                                                     (uu___666_3834.FStar_Syntax_Syntax.lbpos)
                                                 })]), e2));
                                       FStar_Syntax_Syntax.pos =
                                         (uu___664_3819.FStar_Syntax_Syntax.pos);
                                       FStar_Syntax_Syntax.vars =
                                         (uu___664_3819.FStar_Syntax_Syntax.vars)
                                     }
                                   else e_lax
                               | uu____3837 -> e_lax in
                             let uu____3838 =
                               FStar_Util.record_time
                                 (fun uu____3846 ->
                                    let uu____3847 =
                                      let uu____3848 =
                                        let uu____3849 =
                                          FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                            (let uu___670_3858 = env' in
                                             {
                                               FStar_TypeChecker_Env.solver =
                                                 (uu___670_3858.FStar_TypeChecker_Env.solver);
                                               FStar_TypeChecker_Env.range =
                                                 (uu___670_3858.FStar_TypeChecker_Env.range);
                                               FStar_TypeChecker_Env.curmodule
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.curmodule);
                                               FStar_TypeChecker_Env.gamma =
                                                 (uu___670_3858.FStar_TypeChecker_Env.gamma);
                                               FStar_TypeChecker_Env.gamma_sig
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.gamma_sig);
                                               FStar_TypeChecker_Env.gamma_cache
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.gamma_cache);
                                               FStar_TypeChecker_Env.modules
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.modules);
                                               FStar_TypeChecker_Env.expected_typ
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.expected_typ);
                                               FStar_TypeChecker_Env.sigtab =
                                                 (uu___670_3858.FStar_TypeChecker_Env.sigtab);
                                               FStar_TypeChecker_Env.attrtab
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.attrtab);
                                               FStar_TypeChecker_Env.instantiate_imp
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.instantiate_imp);
                                               FStar_TypeChecker_Env.effects
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.effects);
                                               FStar_TypeChecker_Env.generalize
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.generalize);
                                               FStar_TypeChecker_Env.letrecs
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.letrecs);
                                               FStar_TypeChecker_Env.top_level
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.top_level);
                                               FStar_TypeChecker_Env.check_uvars
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.check_uvars);
                                               FStar_TypeChecker_Env.use_eq =
                                                 (uu___670_3858.FStar_TypeChecker_Env.use_eq);
                                               FStar_TypeChecker_Env.use_eq_strict
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.use_eq_strict);
                                               FStar_TypeChecker_Env.is_iface
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.is_iface);
                                               FStar_TypeChecker_Env.admit =
                                                 (uu___670_3858.FStar_TypeChecker_Env.admit);
                                               FStar_TypeChecker_Env.lax =
                                                 true;
                                               FStar_TypeChecker_Env.lax_universes
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.lax_universes);
                                               FStar_TypeChecker_Env.phase1 =
                                                 true;
                                               FStar_TypeChecker_Env.failhard
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.failhard);
                                               FStar_TypeChecker_Env.nosynth
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.nosynth);
                                               FStar_TypeChecker_Env.uvar_subtyping
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.uvar_subtyping);
                                               FStar_TypeChecker_Env.tc_term
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.tc_term);
                                               FStar_TypeChecker_Env.type_of
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.type_of);
                                               FStar_TypeChecker_Env.universe_of
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.universe_of);
                                               FStar_TypeChecker_Env.check_type_of
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.check_type_of);
                                               FStar_TypeChecker_Env.use_bv_sorts
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.use_bv_sorts);
                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.qtbl_name_and_index);
                                               FStar_TypeChecker_Env.normalized_eff_names
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.normalized_eff_names);
                                               FStar_TypeChecker_Env.fv_delta_depths
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.fv_delta_depths);
                                               FStar_TypeChecker_Env.proof_ns
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.proof_ns);
                                               FStar_TypeChecker_Env.synth_hook
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.synth_hook);
                                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                               FStar_TypeChecker_Env.splice =
                                                 (uu___670_3858.FStar_TypeChecker_Env.splice);
                                               FStar_TypeChecker_Env.mpreprocess
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.mpreprocess);
                                               FStar_TypeChecker_Env.postprocess
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.postprocess);
                                               FStar_TypeChecker_Env.identifier_info
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.identifier_info);
                                               FStar_TypeChecker_Env.tc_hooks
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.tc_hooks);
                                               FStar_TypeChecker_Env.dsenv =
                                                 (uu___670_3858.FStar_TypeChecker_Env.dsenv);
                                               FStar_TypeChecker_Env.nbe =
                                                 (uu___670_3858.FStar_TypeChecker_Env.nbe);
                                               FStar_TypeChecker_Env.strict_args_tab
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.strict_args_tab);
                                               FStar_TypeChecker_Env.erasable_types_tab
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.erasable_types_tab);
                                               FStar_TypeChecker_Env.enable_defer_to_tac
                                                 =
                                                 (uu___670_3858.FStar_TypeChecker_Env.enable_defer_to_tac)
                                             }) e in
                                        FStar_All.pipe_right uu____3849
                                          (fun uu____3871 ->
                                             match uu____3871 with
                                             | (e1, uu____3879, uu____3880)
                                                 -> e1) in
                                      FStar_All.pipe_right uu____3848
                                        (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                           env') in
                                    FStar_All.pipe_right uu____3847
                                      drop_lbtyp) in
                             match uu____3838 with
                             | (e1, ms) ->
                                 ((let uu____3886 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env1)
                                       (FStar_Options.Other "TwoPhases") in
                                   if uu____3886
                                   then
                                     let uu____3891 =
                                       FStar_Syntax_Print.term_to_string e1 in
                                     FStar_Util.print1
                                       "Let binding after phase 1: %s\n"
                                       uu____3891
                                   else ());
                                  (let uu____3897 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env1)
                                       (FStar_Options.Other "TCDeclTime") in
                                   if uu____3897
                                   then
                                     let uu____3902 =
                                       FStar_Util.string_of_int ms in
                                     FStar_Util.print1
                                       "Let binding elaborated (phase 1) in %s milliseconds\n"
                                       uu____3902
                                   else ());
                                  e1)
                           else e in
                         let uu____3909 =
                           let uu____3918 =
                             FStar_Syntax_Util.extract_attr'
                               FStar_Parser_Const.postprocess_with
                               se2.FStar_Syntax_Syntax.sigattrs in
                           match uu____3918 with
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
                         (match uu____3909 with
                          | (attrs1, post_tau) ->
                              let se3 =
                                let uu___700_4023 = se2 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___700_4023.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___700_4023.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___700_4023.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___700_4023.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs = attrs1;
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___700_4023.FStar_Syntax_Syntax.sigopts)
                                } in
                              let postprocess_lb tau lb =
                                let lbdef =
                                  FStar_TypeChecker_Env.postprocess env1 tau
                                    lb.FStar_Syntax_Syntax.lbtyp
                                    lb.FStar_Syntax_Syntax.lbdef in
                                let uu___707_4036 = lb in
                                {
                                  FStar_Syntax_Syntax.lbname =
                                    (uu___707_4036.FStar_Syntax_Syntax.lbname);
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___707_4036.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp =
                                    (uu___707_4036.FStar_Syntax_Syntax.lbtyp);
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___707_4036.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = lbdef;
                                  FStar_Syntax_Syntax.lbattrs =
                                    (uu___707_4036.FStar_Syntax_Syntax.lbattrs);
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___707_4036.FStar_Syntax_Syntax.lbpos)
                                } in
                              let uu____4037 =
                                FStar_Util.record_time
                                  (fun uu____4056 ->
                                     FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                       env' e1) in
                              (match uu____4037 with
                               | (r1, ms) ->
                                   ((let uu____4084 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "TCDeclTime") in
                                     if uu____4084
                                     then
                                       let uu____4089 =
                                         FStar_Util.string_of_int ms in
                                       FStar_Util.print1
                                         "Let binding typechecked in phase 2 in %s milliseconds\n"
                                         uu____4089
                                     else ());
                                    (let uu____4094 =
                                       match r1 with
                                       | ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_let
                                              (lbs1, e2);
                                            FStar_Syntax_Syntax.pos =
                                              uu____4119;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4120;_},
                                          uu____4121, g) when
                                           FStar_TypeChecker_Env.is_trivial g
                                           ->
                                           let lbs2 =
                                             let uu____4151 =
                                               FStar_All.pipe_right
                                                 (FStar_Pervasives_Native.snd
                                                    lbs1)
                                                 (FStar_List.map
                                                    rename_parameters) in
                                             ((FStar_Pervasives_Native.fst
                                                 lbs1), uu____4151) in
                                           let lbs3 =
                                             let uu____4175 =
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
                                                 lbs2), uu____4175) in
                                           let quals1 =
                                             match e2.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_meta
                                                 (uu____4198,
                                                  FStar_Syntax_Syntax.Meta_desugared
                                                  (FStar_Syntax_Syntax.Masked_effect))
                                                 ->
                                                 FStar_Syntax_Syntax.HasMaskedEffect
                                                 :: quals
                                             | uu____4203 -> quals in
                                           ((let uu___737_4212 = se3 in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_let
                                                    (lbs3, lids));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___737_4212.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 quals1;
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___737_4212.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___737_4212.FStar_Syntax_Syntax.sigattrs);
                                               FStar_Syntax_Syntax.sigopts =
                                                 (uu___737_4212.FStar_Syntax_Syntax.sigopts)
                                             }), lbs3)
                                       | uu____4215 ->
                                           failwith
                                             "impossible (typechecking should preserve Tm_let)" in
                                     match uu____4094 with
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
                                          (let uu____4271 = log env1 in
                                           if uu____4271
                                           then
                                             let uu____4274 =
                                               let uu____4276 =
                                                 FStar_All.pipe_right
                                                   (FStar_Pervasives_Native.snd
                                                      lbs1)
                                                   (FStar_List.map
                                                      (fun lb ->
                                                         let should_log =
                                                           let uu____4296 =
                                                             let uu____4305 =
                                                               let uu____4306
                                                                 =
                                                                 let uu____4309
                                                                   =
                                                                   FStar_Util.right
                                                                    lb.FStar_Syntax_Syntax.lbname in
                                                                 uu____4309.FStar_Syntax_Syntax.fv_name in
                                                               uu____4306.FStar_Syntax_Syntax.v in
                                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                                               env1
                                                               uu____4305 in
                                                           match uu____4296
                                                           with
                                                           | FStar_Pervasives_Native.None
                                                               -> true
                                                           | uu____4318 ->
                                                               false in
                                                         if should_log
                                                         then
                                                           let uu____4330 =
                                                             FStar_Syntax_Print.lbname_to_string
                                                               lb.FStar_Syntax_Syntax.lbname in
                                                           let uu____4332 =
                                                             FStar_Syntax_Print.term_to_string
                                                               lb.FStar_Syntax_Syntax.lbtyp in
                                                           FStar_Util.format2
                                                             "let %s : %s"
                                                             uu____4330
                                                             uu____4332
                                                         else "")) in
                                               FStar_All.pipe_right
                                                 uu____4276
                                                 (FStar_String.concat "\n") in
                                             FStar_Util.print1 "%s\n"
                                               uu____4274
                                           else ());
                                          check_must_erase_attribute env0 se4;
                                          ([se4], [], env0))))))))
           | FStar_Syntax_Syntax.Sig_polymonadic_bind
               (m, n, p, t, uu____4355) ->
               let t1 =
                 let uu____4357 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env) in
                 if uu____4357
                 then
                   let uu____4360 =
                     let uu____4365 =
                       let uu____4366 =
                         let uu____4367 =
                           FStar_TypeChecker_TcEffect.tc_polymonadic_bind
                             (let uu___762_4374 = env in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___762_4374.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___762_4374.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___762_4374.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___762_4374.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___762_4374.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___762_4374.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___762_4374.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___762_4374.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___762_4374.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___762_4374.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___762_4374.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___762_4374.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___762_4374.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___762_4374.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___762_4374.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___762_4374.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___762_4374.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (uu___762_4374.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___762_4374.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___762_4374.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___762_4374.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___762_4374.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___762_4374.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___762_4374.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___762_4374.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___762_4374.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___762_4374.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___762_4374.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___762_4374.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___762_4374.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___762_4374.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___762_4374.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___762_4374.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___762_4374.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___762_4374.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___762_4374.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (uu___762_4374.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___762_4374.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___762_4374.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___762_4374.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___762_4374.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___762_4374.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___762_4374.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___762_4374.FStar_TypeChecker_Env.erasable_types_tab);
                                FStar_TypeChecker_Env.enable_defer_to_tac =
                                  (uu___762_4374.FStar_TypeChecker_Env.enable_defer_to_tac)
                              }) m n p t in
                         FStar_All.pipe_right uu____4367
                           (fun uu____4385 ->
                              match uu____4385 with
                              | (t1, ty) ->
                                  let uu___767_4392 = se1 in
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (FStar_Syntax_Syntax.Sig_polymonadic_bind
                                         (m, n, p, t1, ty));
                                    FStar_Syntax_Syntax.sigrng =
                                      (uu___767_4392.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals =
                                      (uu___767_4392.FStar_Syntax_Syntax.sigquals);
                                    FStar_Syntax_Syntax.sigmeta =
                                      (uu___767_4392.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (uu___767_4392.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (uu___767_4392.FStar_Syntax_Syntax.sigopts)
                                  }) in
                       FStar_All.pipe_right uu____4366
                         (FStar_TypeChecker_Normalize.elim_uvars env) in
                     FStar_All.pipe_right uu____4365
                       (fun se2 ->
                          match se2.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_polymonadic_bind
                              (uu____4408, uu____4409, uu____4410, t1, ty) ->
                              (t1, ty)
                          | uu____4413 ->
                              failwith
                                "Impossible! tc for Sig_polymonadic_bind must be a Sig_polymonadic_bind") in
                   match uu____4360 with
                   | (t1, ty) ->
                       ((let uu____4422 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "TwoPhases") in
                         if uu____4422
                         then
                           let uu____4427 =
                             FStar_Syntax_Print.sigelt_to_string
                               (let uu___782_4431 = se1 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_polymonadic_bind
                                       (m, n, p, t1, ty));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___782_4431.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___782_4431.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___782_4431.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___782_4431.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___782_4431.FStar_Syntax_Syntax.sigopts)
                                }) in
                           FStar_Util.print1
                             "Polymonadic bind after phase 1: %s\n"
                             uu____4427
                         else ());
                        t1)
                 else t in
               let uu____4437 =
                 FStar_TypeChecker_TcEffect.tc_polymonadic_bind env m n p t1 in
               (match uu____4437 with
                | (t2, ty) ->
                    let se2 =
                      let uu___789_4455 = se1 in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_polymonadic_bind
                             (m, n, p, t2, ty));
                        FStar_Syntax_Syntax.sigrng =
                          (uu___789_4455.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___789_4455.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___789_4455.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___789_4455.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___789_4455.FStar_Syntax_Syntax.sigopts)
                      } in
                    ([se2], [], env0))
           | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
               (m, n, t, uu____4463) ->
               let t1 =
                 let uu____4465 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env) in
                 if uu____4465
                 then
                   let uu____4468 =
                     let uu____4473 =
                       let uu____4474 =
                         let uu____4475 =
                           FStar_TypeChecker_TcEffect.tc_polymonadic_subcomp
                             (let uu___799_4482 = env in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___799_4482.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___799_4482.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___799_4482.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___799_4482.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___799_4482.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___799_4482.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___799_4482.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___799_4482.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___799_4482.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___799_4482.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___799_4482.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___799_4482.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___799_4482.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___799_4482.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___799_4482.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___799_4482.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___799_4482.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (uu___799_4482.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___799_4482.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___799_4482.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___799_4482.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___799_4482.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___799_4482.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___799_4482.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___799_4482.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___799_4482.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___799_4482.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___799_4482.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___799_4482.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___799_4482.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___799_4482.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___799_4482.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___799_4482.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___799_4482.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___799_4482.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___799_4482.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (uu___799_4482.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___799_4482.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___799_4482.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___799_4482.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___799_4482.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___799_4482.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___799_4482.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___799_4482.FStar_TypeChecker_Env.erasable_types_tab);
                                FStar_TypeChecker_Env.enable_defer_to_tac =
                                  (uu___799_4482.FStar_TypeChecker_Env.enable_defer_to_tac)
                              }) m n t in
                         FStar_All.pipe_right uu____4475
                           (fun uu____4493 ->
                              match uu____4493 with
                              | (t1, ty) ->
                                  let uu___804_4500 = se1 in
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                                         (m, n, t1, ty));
                                    FStar_Syntax_Syntax.sigrng =
                                      (uu___804_4500.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals =
                                      (uu___804_4500.FStar_Syntax_Syntax.sigquals);
                                    FStar_Syntax_Syntax.sigmeta =
                                      (uu___804_4500.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (uu___804_4500.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (uu___804_4500.FStar_Syntax_Syntax.sigopts)
                                  }) in
                       FStar_All.pipe_right uu____4474
                         (FStar_TypeChecker_Normalize.elim_uvars env) in
                     FStar_All.pipe_right uu____4473
                       (fun se2 ->
                          match se2.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                              (uu____4515, uu____4516, t1, ty) -> (t1, ty)
                          | uu____4519 ->
                              failwith
                                "Impossible! tc for Sig_polymonadic_subcomp must be a Sig_polymonadic_subcomp") in
                   match uu____4468 with
                   | (t1, ty) ->
                       ((let uu____4528 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "TwoPhases") in
                         if uu____4528
                         then
                           let uu____4533 =
                             FStar_Syntax_Print.sigelt_to_string
                               (let uu___818_4537 = se1 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                                       (m, n, t1, ty));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___818_4537.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___818_4537.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___818_4537.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___818_4537.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___818_4537.FStar_Syntax_Syntax.sigopts)
                                }) in
                           FStar_Util.print1
                             "Polymonadic subcomp after phase 1: %s\n"
                             uu____4533
                         else ());
                        t1)
                 else t in
               let uu____4543 =
                 FStar_TypeChecker_TcEffect.tc_polymonadic_subcomp env m n t1 in
               (match uu____4543 with
                | (t2, ty) ->
                    let se2 =
                      let uu___825_4561 = se1 in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                             (m, n, t2, ty));
                        FStar_Syntax_Syntax.sigrng =
                          (uu___825_4561.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___825_4561.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___825_4561.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___825_4561.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___825_4561.FStar_Syntax_Syntax.sigopts)
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
      (let uu____4599 =
         let uu____4601 =
           FStar_Ident.string_of_lid env1.FStar_TypeChecker_Env.curmodule in
         FStar_Options.debug_module uu____4601 in
       if uu____4599
       then
         let uu____4604 =
           let uu____4606 =
             FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
               (FStar_List.map FStar_Ident.string_of_lid) in
           FStar_All.pipe_right uu____4606 (FStar_String.concat ", ") in
         FStar_Util.print1 "Processing %s\n" uu____4604
       else ());
      (let uu____4625 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____4625
       then
         let uu____4628 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____4628
       else ());
      if (se.FStar_Syntax_Syntax.sigmeta).FStar_Syntax_Syntax.sigmeta_admit
      then
        (let old = FStar_Options.admit_smt_queries () in
         FStar_Options.set_admit_smt_queries true;
         (let result = tc_decl' env1 se in
          FStar_Options.set_admit_smt_queries old; result))
      else tc_decl' env1 se
let for_export :
  'uuuuuu4671 .
    'uuuuuu4671 ->
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
               (fun uu___2_4714 ->
                  match uu___2_4714 with
                  | FStar_Syntax_Syntax.Abstract -> true
                  | uu____4717 -> false)) in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l, uu____4728) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____4736 -> false in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____4746 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_fail uu____4751 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_splice uu____4773 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____4789 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____4815 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses, uu____4841) ->
            let uu____4850 = is_abstract se.FStar_Syntax_Syntax.sigquals in
            if uu____4850
            then
              let for_export_bundle se1 uu____4887 =
                match uu____4887 with
                | (out, hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l, us, bs, t, uu____4926, uu____4927) ->
                         let dec =
                           let uu___884_4937 = se1 in
                           let uu____4938 =
                             let uu____4939 =
                               let uu____4946 =
                                 let uu____4947 =
                                   FStar_Syntax_Syntax.mk_Total t in
                                 FStar_Syntax_Util.arrow bs uu____4947 in
                               (l, us, uu____4946) in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____4939 in
                           {
                             FStar_Syntax_Syntax.sigel = uu____4938;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___884_4937.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___884_4937.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___884_4937.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___884_4937.FStar_Syntax_Syntax.sigopts)
                           } in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l, us, t, uu____4957, uu____4958, uu____4959) ->
                         let dec =
                           let uu___895_4967 = se1 in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___895_4967.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___895_4967.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___895_4967.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___895_4967.FStar_Syntax_Syntax.sigopts)
                           } in
                         ((dec :: out), (l :: hidden1))
                     | uu____4972 -> (out, hidden1)) in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume (uu____4995, uu____4996, uu____4997)
            ->
            let uu____4998 = is_abstract se.FStar_Syntax_Syntax.sigquals in
            if uu____4998 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l, us, t) ->
            let uu____5022 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc) in
            if uu____5022
            then
              ([(let uu___911_5041 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___911_5041.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___911_5041.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___911_5041.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (uu___911_5041.FStar_Syntax_Syntax.sigopts)
                 })], (l :: hidden))
            else
              (let uu____5044 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___3_5050 ->
                         match uu___3_5050 with
                         | FStar_Syntax_Syntax.Assumption -> true
                         | FStar_Syntax_Syntax.Projector uu____5053 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____5059 ->
                             true
                         | uu____5061 -> false)) in
               if uu____5044 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_new_effect uu____5082 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____5087 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____5092 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5109 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____5124 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____5138) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let uu____5152 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
            if uu____5152
            then ([], hidden)
            else
              (let dec =
                 let uu____5173 = FStar_Ident.range_of_lid lid in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____5173;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = [];
                   FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                 } in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs, l) ->
            let uu____5184 = is_abstract se.FStar_Syntax_Syntax.sigquals in
            if uu____5184
            then
              let uu____5195 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb ->
                        let uu___948_5209 = se in
                        let uu____5210 =
                          let uu____5211 =
                            let uu____5218 =
                              let uu____5219 =
                                let uu____5222 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname in
                                uu____5222.FStar_Syntax_Syntax.fv_name in
                              uu____5219.FStar_Syntax_Syntax.v in
                            (uu____5218, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp)) in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____5211 in
                        {
                          FStar_Syntax_Syntax.sigel = uu____5210;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___948_5209.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___948_5209.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___948_5209.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___948_5209.FStar_Syntax_Syntax.sigopts)
                        })) in
              (uu____5195, hidden)
            else ([se], hidden)
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> Prims.bool -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun se ->
      fun from_cache ->
        (let uu____5252 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____5252
         then
           let uu____5255 = FStar_Syntax_Print.sigelt_to_string se in
           let uu____5257 = FStar_Util.string_of_bool from_cache in
           FStar_Util.print2
             ">>>>>>>>>>>>>>Adding top-level decl to environment: %s (from_cache:%s)\n"
             uu____5255 uu____5257
         else ());
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____5262 ->
             let uu____5279 =
               let uu____5285 =
                 let uu____5287 = FStar_Syntax_Print.sigelt_to_string se in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____5287 in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____5285) in
             FStar_Errors.raise_error uu____5279
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_datacon uu____5291 ->
             let uu____5307 =
               let uu____5313 =
                 let uu____5315 = FStar_Syntax_Print.sigelt_to_string se in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____5315 in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____5313) in
             FStar_Errors.raise_error uu____5307
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_declare_typ
             (uu____5319, uu____5320, uu____5321) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___4_5326 ->
                     match uu___4_5326 with
                     | FStar_Syntax_Syntax.OnlyName -> true
                     | uu____5329 -> false))
             -> env
         | FStar_Syntax_Syntax.Sig_let (uu____5331, uu____5332) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___4_5341 ->
                     match uu___4_5341 with
                     | FStar_Syntax_Syntax.OnlyName -> true
                     | uu____5344 -> false))
             -> env
         | uu____5346 ->
             let env1 = FStar_TypeChecker_Env.push_sigelt env se in
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PushOptions uu____5348) ->
                  if from_cache
                  then env1
                  else
                    (let uu___985_5355 = env1 in
                     let uu____5356 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___985_5355.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___985_5355.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___985_5355.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___985_5355.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___985_5355.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___985_5355.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___985_5355.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___985_5355.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___985_5355.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___985_5355.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___985_5355.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___985_5355.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___985_5355.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___985_5355.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___985_5355.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___985_5355.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___985_5355.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___985_5355.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___985_5355.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___985_5355.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___985_5355.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___985_5355.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___985_5355.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___985_5355.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___985_5355.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___985_5355.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___985_5355.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___985_5355.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___985_5355.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___985_5355.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___985_5355.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___985_5355.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___985_5355.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___985_5355.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5356;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___985_5355.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___985_5355.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___985_5355.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___985_5355.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___985_5355.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___985_5355.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___985_5355.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___985_5355.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___985_5355.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___985_5355.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___985_5355.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___985_5355.FStar_TypeChecker_Env.enable_defer_to_tac)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PopOptions) ->
                  if from_cache
                  then env1
                  else
                    (let uu___985_5360 = env1 in
                     let uu____5361 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___985_5360.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___985_5360.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___985_5360.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___985_5360.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___985_5360.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___985_5360.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___985_5360.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___985_5360.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___985_5360.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___985_5360.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___985_5360.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___985_5360.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___985_5360.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___985_5360.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___985_5360.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___985_5360.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___985_5360.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___985_5360.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___985_5360.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___985_5360.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___985_5360.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___985_5360.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___985_5360.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___985_5360.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___985_5360.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___985_5360.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___985_5360.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___985_5360.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___985_5360.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___985_5360.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___985_5360.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___985_5360.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___985_5360.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___985_5360.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5361;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___985_5360.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___985_5360.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___985_5360.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___985_5360.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___985_5360.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___985_5360.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___985_5360.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___985_5360.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___985_5360.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___985_5360.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___985_5360.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___985_5360.FStar_TypeChecker_Env.enable_defer_to_tac)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.SetOptions uu____5362) ->
                  if from_cache
                  then env1
                  else
                    (let uu___985_5367 = env1 in
                     let uu____5368 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___985_5367.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___985_5367.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___985_5367.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___985_5367.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___985_5367.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___985_5367.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___985_5367.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___985_5367.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___985_5367.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___985_5367.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___985_5367.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___985_5367.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___985_5367.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___985_5367.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___985_5367.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___985_5367.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___985_5367.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___985_5367.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___985_5367.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___985_5367.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___985_5367.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___985_5367.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___985_5367.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___985_5367.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___985_5367.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___985_5367.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___985_5367.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___985_5367.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___985_5367.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___985_5367.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___985_5367.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___985_5367.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___985_5367.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___985_5367.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5368;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___985_5367.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___985_5367.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___985_5367.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___985_5367.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___985_5367.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___985_5367.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___985_5367.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___985_5367.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___985_5367.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___985_5367.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___985_5367.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___985_5367.FStar_TypeChecker_Env.enable_defer_to_tac)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.ResetOptions uu____5369) ->
                  if from_cache
                  then env1
                  else
                    (let uu___985_5376 = env1 in
                     let uu____5377 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___985_5376.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___985_5376.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___985_5376.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___985_5376.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___985_5376.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___985_5376.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___985_5376.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___985_5376.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___985_5376.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___985_5376.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___985_5376.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___985_5376.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___985_5376.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___985_5376.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___985_5376.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___985_5376.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___985_5376.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___985_5376.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___985_5376.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___985_5376.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___985_5376.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___985_5376.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___985_5376.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___985_5376.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___985_5376.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___985_5376.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___985_5376.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___985_5376.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___985_5376.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___985_5376.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___985_5376.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___985_5376.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___985_5376.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___985_5376.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5377;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___985_5376.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___985_5376.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___985_5376.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___985_5376.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___985_5376.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___985_5376.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___985_5376.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___985_5376.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___985_5376.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___985_5376.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___985_5376.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___985_5376.FStar_TypeChecker_Env.enable_defer_to_tac)
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
                            let uu____5393 =
                              FStar_Syntax_Util.action_as_lb
                                ne.FStar_Syntax_Syntax.mname a
                                (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Env.push_sigelt env3 uu____5393)
                       env2)
              | FStar_Syntax_Syntax.Sig_sub_effect sub ->
                  FStar_TypeChecker_Util.update_env_sub_eff env1 sub
              | FStar_Syntax_Syntax.Sig_polymonadic_bind
                  (m, n, p, uu____5398, ty) ->
                  FStar_TypeChecker_Util.update_env_polymonadic_bind env1 m n
                    p ty
              | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                  (m, n, uu____5402, ty) ->
                  FStar_TypeChecker_Env.add_polymonadic_subcomp env1 m n ty
              | uu____5404 -> env1))
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun ses ->
      let rec process_one_decl uu____5473 se =
        match uu____5473 with
        | (ses1, exports, env1, hidden) ->
            let uu____5525 =
              env1.FStar_TypeChecker_Env.nosynth &&
                (FStar_Options.debug_any ()) in
            if uu____5525
            then ((ses1, exports, env1, hidden), [])
            else
              ((let uu____5573 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                if uu____5573
                then
                  let uu____5576 = FStar_Syntax_Print.tag_of_sigelt se in
                  let uu____5578 = FStar_Syntax_Print.sigelt_to_string se in
                  FStar_Util.print2
                    ">>>>>>>>>>>>>>Checking top-level %s decl %s\n"
                    uu____5576 uu____5578
                else ());
               (let uu____5583 = tc_decl env1 se in
                match uu____5583 with
                | (ses', ses_elaborated, env2) ->
                    let ses'1 =
                      FStar_All.pipe_right ses'
                        (FStar_List.map
                           (fun se1 ->
                              (let uu____5636 =
                                 FStar_TypeChecker_Env.debug env2
                                   (FStar_Options.Other "UF") in
                               if uu____5636
                               then
                                 let uu____5640 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 FStar_Util.print1
                                   "About to elim vars from %s\n" uu____5640
                               else ());
                              FStar_TypeChecker_Normalize.elim_uvars env2 se1)) in
                    let ses_elaborated1 =
                      FStar_All.pipe_right ses_elaborated
                        (FStar_List.map
                           (fun se1 ->
                              (let uu____5656 =
                                 FStar_TypeChecker_Env.debug env2
                                   (FStar_Options.Other "UF") in
                               if uu____5656
                               then
                                 let uu____5660 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 FStar_Util.print1
                                   "About to elim vars from (elaborated) %s\n"
                                   uu____5660
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
                      (let uu____5678 =
                         (FStar_Options.log_types ()) ||
                           (FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env3)
                              (FStar_Options.Other "LogTypes")) in
                       if uu____5678
                       then
                         let uu____5683 =
                           FStar_List.fold_left
                             (fun s ->
                                fun se1 ->
                                  let uu____5692 =
                                    let uu____5694 =
                                      FStar_Syntax_Print.sigelt_to_string se1 in
                                    Prims.op_Hat uu____5694 "\n" in
                                  Prims.op_Hat s uu____5692) "" ses'1 in
                         FStar_Util.print1 "Checked: %s\n" uu____5683
                       else ());
                      FStar_List.iter
                        (fun se1 ->
                           (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                             env3 se1) ses'1;
                      (let uu____5704 =
                         let uu____5713 =
                           FStar_Options.use_extracted_interfaces () in
                         if uu____5713
                         then ((FStar_List.rev_append ses'1 exports), [])
                         else
                           (let accum_exports_hidden uu____5755 se1 =
                              match uu____5755 with
                              | (exports1, hidden1) ->
                                  let uu____5783 =
                                    for_export env3 hidden1 se1 in
                                  (match uu____5783 with
                                   | (se_exported, hidden2) ->
                                       ((FStar_List.rev_append se_exported
                                           exports1), hidden2)) in
                            FStar_List.fold_left accum_exports_hidden
                              (exports, hidden) ses'1) in
                       match uu____5704 with
                       | (exports1, hidden1) ->
                           (((FStar_List.rev_append ses'1 ses1), exports1,
                              env3, hidden1), ses_elaborated1)))))) in
      let process_one_decl_timed acc se =
        let uu____5937 = acc in
        match uu____5937 with
        | (uu____5972, uu____5973, env1, uu____5975) ->
            let r =
              let uu____6009 =
                let uu____6013 =
                  let uu____6015 = FStar_TypeChecker_Env.current_module env1 in
                  FStar_Ident.string_of_lid uu____6015 in
                FStar_Pervasives_Native.Some uu____6013 in
              FStar_Profiling.profile
                (fun uu____6038 -> process_one_decl acc se) uu____6009
                "FStar.TypeChecker.Tc.process_one_decl" in
            ((let uu____6041 = FStar_Options.profile_group_by_decls () in
              if uu____6041
              then
                let tag =
                  match FStar_Syntax_Util.lids_of_sigelt se with
                  | hd::uu____6048 -> FStar_Ident.string_of_lid hd
                  | uu____6051 ->
                      FStar_Range.string_of_range
                        (FStar_Syntax_Util.range_of_sigelt se) in
                FStar_Profiling.report_and_clear tag
              else ());
             r) in
      let uu____6056 =
        FStar_Syntax_Unionfind.with_uf_enabled
          (fun uu____6086 ->
             FStar_Util.fold_flatten process_one_decl_timed ([], [], env, [])
               ses) in
      match uu____6056 with
      | (ses1, exports, env1, uu____6120) ->
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
          let uu___1087_6236 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1087_6236.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1087_6236.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1087_6236.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1087_6236.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1087_6236.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1087_6236.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1087_6236.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1087_6236.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1087_6236.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1087_6236.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1087_6236.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1087_6236.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1087_6236.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1087_6236.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___1087_6236.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1087_6236.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1087_6236.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1087_6236.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1087_6236.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___1087_6236.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1087_6236.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1087_6236.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1087_6236.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1087_6236.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1087_6236.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1087_6236.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1087_6236.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1087_6236.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1087_6236.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1087_6236.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1087_6236.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1087_6236.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1087_6236.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1087_6236.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1087_6236.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1087_6236.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1087_6236.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1087_6236.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1087_6236.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1087_6236.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1087_6236.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1087_6236.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1087_6236.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1087_6236.FStar_TypeChecker_Env.enable_defer_to_tac)
          } in
        let check_term lid univs t =
          let uu____6256 = FStar_Syntax_Subst.open_univ_vars univs t in
          match uu____6256 with
          | (univs1, t1) ->
              ((let uu____6264 =
                  let uu____6266 =
                    let uu____6272 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____6272 in
                  FStar_All.pipe_left uu____6266
                    (FStar_Options.Other "Exports") in
                if uu____6264
                then
                  let uu____6276 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____6278 =
                    let uu____6280 =
                      FStar_All.pipe_right univs1
                        (FStar_List.map
                           (fun x ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____6280
                      (FStar_String.concat ", ") in
                  let uu____6297 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____6276 uu____6278 uu____6297
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs1 in
                let uu____6303 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____6303 (fun uu____6312 -> ()))) in
        let check_term1 lid univs t =
          (let uu____6330 =
             let uu____6332 =
               FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
             let uu____6334 = FStar_Ident.string_of_lid lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____6332 uu____6334 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____6330);
          check_term lid univs t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses, uu____6345) ->
              let uu____6354 =
                let uu____6356 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____6356 in
              if uu____6354
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l, univs, binders, typ, uu____6370, uu____6371) ->
              let t =
                let uu____6383 =
                  let uu____6384 =
                    let uu____6399 = FStar_Syntax_Syntax.mk_Total typ in
                    (binders, uu____6399) in
                  FStar_Syntax_Syntax.Tm_arrow uu____6384 in
                FStar_Syntax_Syntax.mk uu____6383
                  se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs t
          | FStar_Syntax_Syntax.Sig_datacon
              (l, univs, t, uu____6415, uu____6416, uu____6417) ->
              check_term1 l univs t
          | FStar_Syntax_Syntax.Sig_declare_typ (l, univs, t) ->
              let uu____6427 =
                let uu____6429 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____6429 in
              if uu____6427 then check_term1 l univs t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____6437, lbs), uu____6439) ->
              let uu____6450 =
                let uu____6452 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____6452 in
              if uu____6450
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
              let uu____6475 =
                let uu____6477 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____6477 in
              if uu____6475
              then
                let arrow =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs arrow
              else ()
          | FStar_Syntax_Syntax.Sig_assume uu____6498 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____6505 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____6506 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____6507 -> ()
          | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____6508 -> ()
          | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____6519 -> ()
          | FStar_Syntax_Syntax.Sig_fail uu____6528 ->
              failwith "Impossible (Already handled)"
          | FStar_Syntax_Syntax.Sig_splice uu____6542 ->
              failwith "Impossible (Already handled)" in
        let uu____6550 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid in
        if uu____6550 then () else FStar_List.iter check_sigelt exports
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
             | FStar_Syntax_Syntax.Projector (l, uu____6656) -> true
             | uu____6658 -> false) quals in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____6688 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs', c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c)) r
               | uu____6727 ->
                   let uu____6728 =
                     let uu____6729 =
                       let uu____6744 = FStar_Syntax_Syntax.mk_Total t in
                       (bs, uu____6744) in
                     FStar_Syntax_Syntax.Tm_arrow uu____6729 in
                   FStar_Syntax_Syntax.mk uu____6728 r) in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid, uvs, bs, t, uu____6761, uu____6762) ->
            let s1 =
              let uu___1215_6772 = s in
              let uu____6773 =
                let uu____6774 =
                  let uu____6781 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng in
                  (lid, uvs, uu____6781) in
                FStar_Syntax_Syntax.Sig_declare_typ uu____6774 in
              let uu____6782 =
                let uu____6785 =
                  let uu____6788 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals in
                  FStar_Syntax_Syntax.New :: uu____6788 in
                FStar_Syntax_Syntax.Assumption :: uu____6785 in
              {
                FStar_Syntax_Syntax.sigel = uu____6773;
                FStar_Syntax_Syntax.sigrng =
                  (uu___1215_6772.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____6782;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___1215_6772.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___1215_6772.FStar_Syntax_Syntax.sigattrs);
                FStar_Syntax_Syntax.sigopts =
                  (uu___1215_6772.FStar_Syntax_Syntax.sigopts)
              } in
            [s1]
        | uu____6791 -> failwith "Impossible!" in
      let val_of_lb s lid uu____6816 lbdef =
        match uu____6816 with
        | (uvs, t) ->
            let attrs =
              let uu____6827 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef in
              if uu____6827
              then
                let uu____6832 =
                  let uu____6833 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None in
                  FStar_All.pipe_right uu____6833
                    FStar_Syntax_Syntax.fv_to_tm in
                uu____6832 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs in
            let uu___1228_6836 = s in
            let uu____6837 =
              let uu____6840 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals in
              FStar_Syntax_Syntax.Assumption :: uu____6840 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___1228_6836.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____6837;
              FStar_Syntax_Syntax.sigmeta =
                (uu___1228_6836.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs;
              FStar_Syntax_Syntax.sigopts =
                (uu___1228_6836.FStar_Syntax_Syntax.sigopts)
            } in
      let should_keep_lbdef t =
        let comp_effect_name c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____6858 -> failwith "Impossible!" in
        let c_opt =
          let uu____6865 = FStar_Syntax_Util.is_unit t in
          if uu____6865
          then
            let uu____6872 = FStar_Syntax_Syntax.mk_Total t in
            FStar_Pervasives_Native.Some uu____6872
          else
            (let uu____6879 =
               let uu____6880 = FStar_Syntax_Subst.compress t in
               uu____6880.FStar_Syntax_Syntax.n in
             match uu____6879 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____6887, c) ->
                 FStar_Pervasives_Native.Some c
             | uu____6911 -> FStar_Pervasives_Native.None) in
        match c_opt with
        | FStar_Pervasives_Native.None -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____6923 = FStar_Syntax_Util.is_lemma_comp c in
            if uu____6923
            then false
            else
              (let uu____6930 = FStar_Syntax_Util.is_pure_or_ghost_comp c in
               if uu____6930
               then true
               else
                 (let uu____6937 = comp_effect_name c in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____6937)) in
      let extract_sigelt s =
        (let uu____6949 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme in
         if uu____6949
         then
           let uu____6952 = FStar_Syntax_Print.sigelt_to_string s in
           FStar_Util.print1 "Extracting interface for %s\n" uu____6952
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____6959 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____6979 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____6998 ->
             failwith
               "Impossible! extract_interface: trying to extract splice"
         | FStar_Syntax_Syntax.Sig_fail uu____7008 ->
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
                             (lid, uu____7060, uu____7061, uu____7062,
                              uu____7063, uu____7064)
                             ->
                             ((let uu____7074 =
                                 let uu____7077 =
                                   FStar_ST.op_Bang abstract_inductive_tycons in
                                 lid :: uu____7077 in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____7074);
                              (let uu____7126 = vals_of_abstract_inductive s1 in
                               FStar_List.append uu____7126 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid, uu____7130, uu____7131, uu____7132,
                              uu____7133, uu____7134)
                             ->
                             ((let uu____7142 =
                                 let uu____7145 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons in
                                 lid :: uu____7145 in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____7142);
                              sigelts1)
                         | uu____7194 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) ->
             let uu____7203 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals in
             if uu____7203
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____7213 =
                    let uu___1294_7214 = s in
                    let uu____7215 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1294_7214.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1294_7214.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____7215;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1294_7214.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1294_7214.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1294_7214.FStar_Syntax_Syntax.sigopts)
                    } in
                  [uu____7213])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs, lids) ->
             let uu____7226 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals in
             if uu____7226
             then []
             else
               (let uu____7233 = lbs in
                match uu____7233 with
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
                        (fun uu____7295 ->
                           match uu____7295 with
                           | (uu____7303, t, uu____7305) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs in
                    let vals =
                      FStar_List.map2
                        (fun lid ->
                           fun uu____7322 ->
                             match uu____7322 with
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
                           (fun uu____7349 ->
                              match uu____7349 with
                              | (uu____7357, t, uu____7359) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_assume (lid, uu____7367, uu____7368) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____7376 = FStar_ST.op_Bang abstract_inductive_tycons in
                 FStar_List.existsML
                   (fun l ->
                      let uu____7405 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l in
                      FStar_Ident.lid_equals lid uu____7405) uu____7376 in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____7409 =
                    let uu___1334_7410 = s in
                    let uu____7411 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1334_7410.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1334_7410.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____7411;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1334_7410.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1334_7410.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1334_7410.FStar_Syntax_Syntax.sigopts)
                    } in
                  [uu____7409]
                else [])
             else
               (let uu____7418 =
                  let uu___1336_7419 = s in
                  let uu____7420 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1336_7419.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1336_7419.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____7420;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1336_7419.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1336_7419.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___1336_7419.FStar_Syntax_Syntax.sigopts)
                  } in
                [uu____7418])
         | FStar_Syntax_Syntax.Sig_new_effect uu____7423 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____7424 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7425 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____7438 -> [s]
         | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____7439 -> [s]
         | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____7450 -> [s]) in
      let uu___1350_7459 = m in
      let uu____7460 =
        let uu____7461 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt) in
        FStar_All.pipe_right uu____7461 FStar_List.flatten in
      {
        FStar_Syntax_Syntax.name = (uu___1350_7459.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____7460;
        FStar_Syntax_Syntax.exports =
          (uu___1350_7459.FStar_Syntax_Syntax.exports);
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
        (fun uu____7512 -> FStar_TypeChecker_Env.snapshot env msg)
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
          (fun uu____7559 ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth in env)
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env ->
    fun msg ->
      let uu____7574 = snapshot_context env msg in
      FStar_Pervasives_Native.snd uu____7574
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
        let uu____7646 =
          FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
        FStar_Options.should_verify uu____7646 in
      let action = if verify then "Verifying" else "Lax-checking" in
      let label =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation" in
      (let uu____7665 = FStar_Options.debug_any () in
       if uu____7665
       then
         let uu____7668 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
         FStar_Util.print3 "%s %s of %s\n" action label uu____7668
       else ());
      (let name =
         let uu____7675 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") uu____7675 in
       let env1 =
         let uu___1375_7685 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___1375_7685.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___1375_7685.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___1375_7685.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___1375_7685.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___1375_7685.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___1375_7685.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___1375_7685.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___1375_7685.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___1375_7685.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___1375_7685.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___1375_7685.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___1375_7685.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___1375_7685.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___1375_7685.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___1375_7685.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___1375_7685.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___1375_7685.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___1375_7685.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___1375_7685.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___1375_7685.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___1375_7685.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___1375_7685.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___1375_7685.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___1375_7685.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___1375_7685.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___1375_7685.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___1375_7685.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___1375_7685.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___1375_7685.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___1375_7685.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___1375_7685.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___1375_7685.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___1375_7685.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___1375_7685.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___1375_7685.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___1375_7685.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___1375_7685.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___1375_7685.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___1375_7685.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___1375_7685.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___1375_7685.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___1375_7685.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___1375_7685.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___1375_7685.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___1375_7685.FStar_TypeChecker_Env.enable_defer_to_tac)
         } in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name in
       let uu____7687 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
       match uu____7687 with
       | (ses, exports, env3) ->
           ((let uu___1383_7720 = modul in
             {
               FStar_Syntax_Syntax.name =
                 (uu___1383_7720.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___1383_7720.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___1383_7720.FStar_Syntax_Syntax.is_interface)
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
        let uu____7749 = tc_decls env decls in
        match uu____7749 with
        | (ses, exports, env1) ->
            let modul1 =
              let uu___1392_7780 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___1392_7780.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___1392_7780.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___1392_7780.FStar_Syntax_Syntax.is_interface)
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
          let uu____7839 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
          Prims.op_Hat "Internals for " uu____7839 in
        let env01 = push_context env0 msg in
        let uu____7843 = tc_partial_modul env01 m in
        match uu____7843 with
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
                (let uu____7880 = FStar_Errors.get_err_count () in
                 uu____7880 = Prims.int_zero) in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m in
              ((let uu____7891 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low in
                if uu____7891
                then
                  let uu____7895 =
                    FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                  let uu____7897 =
                    let uu____7899 =
                      let uu____7901 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                      FStar_Options.should_verify uu____7901 in
                    if uu____7899 then "" else " (in lax mode) " in
                  let uu____7909 =
                    let uu____7911 =
                      let uu____7913 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                      FStar_Options.dump_module uu____7913 in
                    if uu____7911
                    then
                      let uu____7917 =
                        let uu____7919 = FStar_Syntax_Print.modul_to_string m in
                        Prims.op_Hat uu____7919 "\n" in
                      Prims.op_Hat "\nfrom: " uu____7917
                    else "" in
                  let uu____7926 =
                    let uu____7928 =
                      let uu____7930 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                      FStar_Options.dump_module uu____7930 in
                    if uu____7928
                    then
                      let uu____7934 =
                        let uu____7936 =
                          FStar_Syntax_Print.modul_to_string modul_iface in
                        Prims.op_Hat uu____7936 "\n" in
                      Prims.op_Hat "\nto: " uu____7934
                    else "" in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    uu____7895 uu____7897 uu____7909 uu____7926
                else ());
               (let en0 =
                  let en0 =
                    let uu____7948 =
                      let uu____7950 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                      Prims.op_Hat "Ending modul " uu____7950 in
                    pop_context en uu____7948 in
                  let en01 =
                    let uu___1418_7954 = en0 in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1418_7954.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1418_7954.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1418_7954.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1418_7954.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1418_7954.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1418_7954.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1418_7954.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1418_7954.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1418_7954.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1418_7954.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1418_7954.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1418_7954.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1418_7954.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1418_7954.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1418_7954.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1418_7954.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1418_7954.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.use_eq_strict =
                        (uu___1418_7954.FStar_TypeChecker_Env.use_eq_strict);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1418_7954.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1418_7954.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1418_7954.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1418_7954.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1418_7954.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1418_7954.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1418_7954.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1418_7954.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1418_7954.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1418_7954.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1418_7954.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1418_7954.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1418_7954.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1418_7954.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1418_7954.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1418_7954.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1418_7954.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1418_7954.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1418_7954.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1418_7954.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.mpreprocess =
                        (uu___1418_7954.FStar_TypeChecker_Env.mpreprocess);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1418_7954.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1418_7954.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1418_7954.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1418_7954.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1418_7954.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___1418_7954.FStar_TypeChecker_Env.erasable_types_tab);
                      FStar_TypeChecker_Env.enable_defer_to_tac =
                        (uu___1418_7954.FStar_TypeChecker_Env.enable_defer_to_tac)
                    } in
                  let en02 =
                    let uu___1421_7956 = en01 in
                    let uu____7957 =
                      let uu____7972 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst in
                      (uu____7972, FStar_Pervasives_Native.None) in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1421_7956.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1421_7956.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1421_7956.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1421_7956.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1421_7956.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1421_7956.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1421_7956.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1421_7956.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1421_7956.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1421_7956.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1421_7956.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1421_7956.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1421_7956.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1421_7956.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1421_7956.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1421_7956.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1421_7956.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.use_eq_strict =
                        (uu___1421_7956.FStar_TypeChecker_Env.use_eq_strict);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1421_7956.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1421_7956.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1421_7956.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1421_7956.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1421_7956.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1421_7956.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1421_7956.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1421_7956.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1421_7956.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1421_7956.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1421_7956.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1421_7956.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1421_7956.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____7957;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1421_7956.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1421_7956.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1421_7956.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1421_7956.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1421_7956.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1421_7956.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.mpreprocess =
                        (uu___1421_7956.FStar_TypeChecker_Env.mpreprocess);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1421_7956.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1421_7956.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1421_7956.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1421_7956.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1421_7956.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1421_7956.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___1421_7956.FStar_TypeChecker_Env.erasable_types_tab);
                      FStar_TypeChecker_Env.enable_defer_to_tac =
                        (uu___1421_7956.FStar_TypeChecker_Env.enable_defer_to_tac)
                    } in
                  let uu____8018 =
                    let uu____8020 = FStar_Options.interactive () in
                    Prims.op_Negation uu____8020 in
                  if uu____8018
                  then
                    ((let uu____8024 =
                        FStar_Options.restore_cmd_line_options true in
                      FStar_All.pipe_right uu____8024 (fun uu____8026 -> ()));
                     en02)
                  else en02 in
                let uu____8029 = tc_modul en0 modul_iface true in
                match uu____8029 with
                | (modul_iface1, env) ->
                    ((let uu___1430_8042 = m in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___1430_8042.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___1430_8042.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___1430_8042.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___1432_8046 = m in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___1432_8046.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___1432_8046.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___1432_8046.FStar_Syntax_Syntax.is_interface)
                 } in
               let env = FStar_TypeChecker_Env.finish_module en modul in
               (let uu____8049 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____8049 FStar_Util.smap_clear);
               (let uu____8085 =
                  ((let uu____8089 = FStar_Options.lax () in
                    Prims.op_Negation uu____8089) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____8092 =
                       FStar_Options.use_extracted_interfaces () in
                     Prims.op_Negation uu____8092) in
                if uu____8085
                then
                  FStar_Syntax_Unionfind.with_uf_enabled
                    (fun uu____8096 -> check_exports env modul exports)
                else ());
               (let uu____8100 =
                  let uu____8101 =
                    let uu____8103 =
                      FStar_Ident.string_of_lid
                        modul.FStar_Syntax_Syntax.name in
                    Prims.op_Hat "Ending modul " uu____8103 in
                  pop_context env uu____8101 in
                FStar_All.pipe_right uu____8100 (fun uu____8106 -> ()));
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
        let uu____8120 =
          let uu____8122 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
          Prims.op_Hat "Internals for " uu____8122 in
        push_context env uu____8120 in
      let env2 =
        FStar_List.fold_left
          (fun env2 ->
             fun se ->
               let env3 = add_sigelt_to_env env2 se true in
               let lids = FStar_Syntax_Util.lids_of_sigelt se in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid ->
                       let uu____8144 =
                         FStar_TypeChecker_Env.lookup_sigelt env3 lid in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations in
      let uu____8147 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports in
      match uu____8147 with | (uu____8154, env3) -> env3
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun m ->
      fun b ->
        (let uu____8179 = FStar_Options.debug_any () in
         if uu____8179
         then
           let uu____8182 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____8182
         else ());
        (let uu____8194 =
           let uu____8196 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
           FStar_Options.dump_module uu____8196 in
         if uu____8194
         then
           let uu____8199 = FStar_Syntax_Print.modul_to_string m in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____8199
         else ());
        (let env1 =
           let uu___1463_8205 = env in
           let uu____8206 =
             let uu____8208 =
               let uu____8210 =
                 FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
               FStar_Options.should_verify uu____8210 in
             Prims.op_Negation uu____8208 in
           {
             FStar_TypeChecker_Env.solver =
               (uu___1463_8205.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___1463_8205.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___1463_8205.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___1463_8205.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___1463_8205.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___1463_8205.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___1463_8205.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___1463_8205.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___1463_8205.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___1463_8205.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___1463_8205.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___1463_8205.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___1463_8205.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___1463_8205.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___1463_8205.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___1463_8205.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___1463_8205.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.use_eq_strict =
               (uu___1463_8205.FStar_TypeChecker_Env.use_eq_strict);
             FStar_TypeChecker_Env.is_iface =
               (uu___1463_8205.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___1463_8205.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____8206;
             FStar_TypeChecker_Env.lax_universes =
               (uu___1463_8205.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___1463_8205.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___1463_8205.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___1463_8205.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___1463_8205.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___1463_8205.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___1463_8205.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___1463_8205.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___1463_8205.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___1463_8205.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___1463_8205.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___1463_8205.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___1463_8205.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___1463_8205.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___1463_8205.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___1463_8205.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___1463_8205.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (uu___1463_8205.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (uu___1463_8205.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.identifier_info =
               (uu___1463_8205.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___1463_8205.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___1463_8205.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___1463_8205.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___1463_8205.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___1463_8205.FStar_TypeChecker_Env.erasable_types_tab);
             FStar_TypeChecker_Env.enable_defer_to_tac =
               (uu___1463_8205.FStar_TypeChecker_Env.enable_defer_to_tac)
           } in
         let uu____8212 = tc_modul env1 m b in
         match uu____8212 with
         | (m1, env2) ->
             ((let uu____8224 =
                 let uu____8226 =
                   FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name in
                 FStar_Options.dump_module uu____8226 in
               if uu____8224
               then
                 let uu____8229 = FStar_Syntax_Print.modul_to_string m1 in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____8229
               else ());
              (let uu____8235 =
                 (let uu____8239 =
                    FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name in
                  FStar_Options.dump_module uu____8239) &&
                   (let uu____8242 =
                      FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name in
                    FStar_Options.debug_at_level uu____8242
                      (FStar_Options.Other "Normalize")) in
               if uu____8235
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
                         let uu____8280 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef in
                         match uu____8280 with
                         | (univnames, e) ->
                             let uu___1485_8287 = lb in
                             let uu____8288 =
                               let uu____8291 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames in
                               n uu____8291 e in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1485_8287.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1485_8287.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1485_8287.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1485_8287.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____8288;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1485_8287.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1485_8287.FStar_Syntax_Syntax.lbpos)
                             } in
                       let uu___1487_8292 = se in
                       let uu____8293 =
                         let uu____8294 =
                           let uu____8301 =
                             let uu____8302 = FStar_List.map update lbs in
                             (b1, uu____8302) in
                           (uu____8301, ids) in
                         FStar_Syntax_Syntax.Sig_let uu____8294 in
                       {
                         FStar_Syntax_Syntax.sigel = uu____8293;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1487_8292.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1487_8292.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1487_8292.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___1487_8292.FStar_Syntax_Syntax.sigattrs);
                         FStar_Syntax_Syntax.sigopts =
                           (uu___1487_8292.FStar_Syntax_Syntax.sigopts)
                       }
                   | uu____8310 -> se in
                 let normalized_module =
                   let uu___1491_8312 = m1 in
                   let uu____8313 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___1491_8312.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____8313;
                     FStar_Syntax_Syntax.exports =
                       (uu___1491_8312.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___1491_8312.FStar_Syntax_Syntax.is_interface)
                   } in
                 let uu____8314 =
                   FStar_Syntax_Print.modul_to_string normalized_module in
                 FStar_Util.print1 "%s\n" uu____8314
               else ());
              (m1, env2)))