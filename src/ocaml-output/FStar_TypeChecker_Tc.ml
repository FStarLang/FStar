open Prims
let (set_hint_correlator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      let tbl =
        FStar_All.pipe_right env.FStar_TypeChecker_Env.qtbl_name_and_index
          FStar_Pervasives_Native.fst
         in
      let get_n lid =
        let n_opt =
          let uu____52 = FStar_Ident.string_of_lid lid  in
          FStar_Util.smap_try_find tbl uu____52  in
        if FStar_Util.is_some n_opt
        then FStar_All.pipe_right n_opt FStar_Util.must
        else Prims.int_zero  in
      let uu____66 = FStar_Options.reuse_hint_for ()  in
      match uu____66 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____74 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.lid_add_suffix uu____74 l  in
          let uu___15_75 = env  in
          let uu____76 =
            let uu____91 =
              let uu____99 = let uu____105 = get_n lid  in (lid, uu____105)
                 in
              FStar_Pervasives_Native.Some uu____99  in
            (tbl, uu____91)  in
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
              (uu___15_75.FStar_TypeChecker_Env.erasable_types_tab)
          }
      | FStar_Pervasives_Native.None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          let lid =
            match lids with
            | [] ->
                let uu____128 = FStar_TypeChecker_Env.current_module env  in
                let uu____129 =
                  let uu____131 = FStar_Ident.next_id ()  in
                  FStar_All.pipe_right uu____131 FStar_Util.string_of_int  in
                FStar_Ident.lid_add_suffix uu____128 uu____129
            | l::uu____136 -> l  in
          let uu___24_139 = env  in
          let uu____140 =
            let uu____155 =
              let uu____163 = let uu____169 = get_n lid  in (lid, uu____169)
                 in
              FStar_Pervasives_Native.Some uu____163  in
            (tbl, uu____155)  in
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
              (uu___24_139.FStar_TypeChecker_Env.erasable_types_tab)
          }
  
let (log : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____195 =
         let uu____197 = FStar_TypeChecker_Env.current_module env  in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____197  in
       Prims.op_Negation uu____195)
  
let tc_lex_t :
  'uuuuuu209 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'uuuuuu209 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____244 = FStar_List.hd ses  in
            uu____244.FStar_Syntax_Syntax.sigrng  in
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
                 (lex_t,uu____255,[],t,uu____257,uu____258);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____260;
               FStar_Syntax_Syntax.sigattrs = uu____261;
               FStar_Syntax_Syntax.sigopts = uu____262;_}::{
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               FStar_Syntax_Syntax.Sig_datacon
                                                               (lex_top,uu____264,_t_top,_lex_t_top,uu____302,uu____267);
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
                   (lex_cons,uu____273,_t_cons,_lex_t_cons,uu____312,uu____276);
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
                   (FStar_Pervasives_Native.Some r)
                  in
               let t1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_type
                      (FStar_Syntax_Syntax.U_name u))
                   FStar_Pervasives_Native.None r
                  in
               let t2 = FStar_Syntax_Subst.close_univ_vars [u] t1  in
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
                 }  in
               let utop =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r1)
                  in
               let lex_top_t =
                 let uu____339 =
                   let uu____346 =
                     let uu____347 =
                       let uu____354 =
                         let uu____357 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____357
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____354, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____347  in
                   FStar_Syntax_Syntax.mk uu____346  in
                 uu____339 FStar_Pervasives_Native.None r1  in
               let lex_top_t1 =
                 FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t  in
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
                 }  in
               let ucons1 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2)
                  in
               let ucons2 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2)
                  in
               let lex_cons_t =
                 let a =
                   let uu____372 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____372
                    in
                 let hd =
                   let uu____374 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____374
                    in
                 let tl =
                   let uu____376 =
                     let uu____377 =
                       let uu____384 =
                         let uu____385 =
                           let uu____392 =
                             let uu____395 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____395
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____392, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____385  in
                       FStar_Syntax_Syntax.mk uu____384  in
                     uu____377 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____376
                    in
                 let res =
                   let uu____401 =
                     let uu____408 =
                       let uu____409 =
                         let uu____416 =
                           let uu____419 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____419
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____416,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____409  in
                     FStar_Syntax_Syntax.mk uu____408  in
                   uu____401 FStar_Pervasives_Native.None r2  in
                 let uu____422 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd, FStar_Pervasives_Native.None);
                   (tl, FStar_Pervasives_Native.None)] uu____422
                  in
               let lex_cons_t1 =
                 FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                   lex_cons_t
                  in
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
                 }  in
               let uu____461 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____461;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = [];
                 FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
               }
           | uu____466 ->
               let err_msg =
                 let uu____471 =
                   let uu____473 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____473  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____471
                  in
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT, err_msg)
                 err_range)
  
let (tc_type_common :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Syntax_Syntax.typ ->
        FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun uu____498  ->
      fun expected_typ  ->
        fun r  ->
          match uu____498 with
          | (uvs,t) ->
              let uu____511 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____511 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 =
                     FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t1
                       expected_typ
                      in
                   if uvs1 = []
                   then
                     let uu____523 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____523 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____541 =
                        let uu____544 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____544
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____541)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____567 =
          let uu____568 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____568 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____567 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____593 =
          let uu____594 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____594 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____593 r
  
let (tc_inductive' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.attribute Prims.list ->
          FStar_Ident.lident Prims.list ->
            (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
              Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          fun lids  ->
            (let uu____652 =
               FStar_TypeChecker_Env.debug env FStar_Options.Low  in
             if uu____652
             then
               let uu____655 =
                 FStar_Common.string_of_list
                   FStar_Syntax_Print.sigelt_to_string ses
                  in
               FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____655
             else ());
            (let uu____660 =
               FStar_TypeChecker_TcInductive.check_inductive_well_typedness
                 env ses quals lids
                in
             match uu____660 with
             | (sig_bndle,tcs,datas) ->
                 let attrs' =
                   FStar_Syntax_Util.remove_attr
                     FStar_Parser_Const.erasable_attr attrs
                    in
                 let data_ops_ses =
                   let uu____694 =
                     FStar_List.map
                       (FStar_TypeChecker_TcInductive.mk_data_operations
                          quals attrs' env tcs) datas
                      in
                   FStar_All.pipe_right uu____694 FStar_List.flatten  in
                 ((let uu____708 =
                     (FStar_Options.no_positivity ()) ||
                       (let uu____711 =
                          FStar_TypeChecker_Env.should_verify env  in
                        Prims.op_Negation uu____711)
                      in
                   if uu____708
                   then ()
                   else
                     (let env1 =
                        FStar_TypeChecker_Env.push_sigelt env sig_bndle  in
                      FStar_List.iter
                        (fun ty  ->
                           let b =
                             FStar_TypeChecker_TcInductive.check_positivity
                               ty env1
                              in
                           if Prims.op_Negation b
                           then
                             let uu____728 =
                               match ty.FStar_Syntax_Syntax.sigel with
                               | FStar_Syntax_Syntax.Sig_inductive_typ
                                   (lid,uu____738,uu____739,uu____740,uu____741,uu____742)
                                   -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                               | uu____751 -> failwith "Impossible!"  in
                             match uu____728 with
                             | (lid,r) ->
                                 let uu____759 =
                                   let uu____765 =
                                     let uu____767 =
                                       let uu____769 =
                                         FStar_Ident.string_of_lid lid  in
                                       Prims.op_Hat uu____769
                                         " does not satisfy the positivity condition"
                                        in
                                     Prims.op_Hat "Inductive type " uu____767
                                      in
                                   (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                     uu____765)
                                    in
                                 FStar_Errors.log_issue r uu____759
                           else ()) tcs;
                      FStar_List.iter
                        (fun d  ->
                           let uu____783 =
                             match d.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (data_lid,uu____793,uu____794,ty_lid,uu____796,uu____797)
                                 -> (data_lid, ty_lid)
                             | uu____804 -> failwith "Impossible"  in
                           match uu____783 with
                           | (data_lid,ty_lid) ->
                               let uu____812 =
                                 (FStar_Ident.lid_equals ty_lid
                                    FStar_Parser_Const.exn_lid)
                                   &&
                                   (let uu____815 =
                                      FStar_TypeChecker_TcInductive.check_exn_positivity
                                        data_lid env1
                                       in
                                    Prims.op_Negation uu____815)
                                  in
                               if uu____812
                               then
                                 let uu____818 =
                                   let uu____824 =
                                     let uu____826 =
                                       let uu____828 =
                                         FStar_Ident.string_of_lid data_lid
                                          in
                                       Prims.op_Hat uu____828
                                         " does not satisfy the positivity condition"
                                        in
                                     Prims.op_Hat "Exception " uu____826  in
                                   (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                     uu____824)
                                    in
                                 FStar_Errors.log_issue
                                   d.FStar_Syntax_Syntax.sigrng uu____818
                               else ()) datas));
                  (let skip_haseq =
                     let skip_prims_type uu____843 =
                       let lid =
                         let ty = FStar_List.hd tcs  in
                         match ty.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_inductive_typ
                             (lid,uu____848,uu____849,uu____850,uu____851,uu____852)
                             -> lid
                         | uu____861 -> failwith "Impossible"  in
                       FStar_List.existsb
                         (fun s  ->
                            let uu____868 =
                              let uu____870 = FStar_Ident.ident_of_lid lid
                                 in
                              FStar_Ident.text_of_id uu____870  in
                            s = uu____868)
                         FStar_TypeChecker_TcInductive.early_prims_inductives
                        in
                     let is_noeq =
                       FStar_List.existsb
                         (fun q  -> q = FStar_Syntax_Syntax.Noeq) quals
                        in
                     let is_erasable uu____882 =
                       let uu____883 =
                         let uu____886 = FStar_List.hd tcs  in
                         uu____886.FStar_Syntax_Syntax.sigattrs  in
                       FStar_Syntax_Util.has_attribute uu____883
                         FStar_Parser_Const.erasable_attr
                        in
                     ((((FStar_List.length tcs) = Prims.int_zero) ||
                         ((FStar_Ident.lid_equals
                             env.FStar_TypeChecker_Env.curmodule
                             FStar_Parser_Const.prims_lid)
                            && (skip_prims_type ())))
                        || is_noeq)
                       || (is_erasable ())
                      in
                   let res =
                     if skip_haseq
                     then (sig_bndle, data_ops_ses)
                     else
                       (let is_unopteq =
                          FStar_List.existsb
                            (fun q  -> q = FStar_Syntax_Syntax.Unopteq) quals
                           in
                        let ses1 =
                          if is_unopteq
                          then
                            FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                              sig_bndle tcs datas env
                          else
                            FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                              sig_bndle tcs datas env
                           in
                        (sig_bndle, (FStar_List.append ses1 data_ops_ses)))
                      in
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
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          fun lids  ->
            let env1 = FStar_TypeChecker_Env.push env "tc_inductive"  in
            let pop uu____976 =
              let uu____977 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
                 in
              ()  in
            try
              (fun uu___203_987  ->
                 match () with
                 | () ->
                     let uu____994 = tc_inductive' env1 ses quals attrs lids
                        in
                     FStar_All.pipe_right uu____994 (fun r  -> pop (); r)) ()
            with | uu___202_1025 -> (pop (); FStar_Exn.raise uu___202_1025)
  
let (check_must_erase_attribute :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
          let uu____1056 =
            let uu____1058 = FStar_Options.ide ()  in
            Prims.op_Negation uu____1058  in
          if uu____1056
          then
            let uu____1061 =
              let uu____1066 = FStar_TypeChecker_Env.dsenv env  in
              let uu____1067 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____1066 uu____1067  in
            (match uu____1061 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some iface_decls ->
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.iter
                      (fun lb  ->
                         let lbname =
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                         let has_iface_val =
                           let uu____1091 =
                             let uu____1099 =
                               let uu____1105 =
                                 FStar_Ident.ident_of_lid
                                   (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  in
                               FStar_Parser_AST.decl_is_val uu____1105  in
                             FStar_Util.for_some uu____1099  in
                           FStar_All.pipe_right iface_decls uu____1091  in
                         if has_iface_val
                         then
                           let must_erase =
                             FStar_TypeChecker_Util.must_erase_for_extraction
                               env lb.FStar_Syntax_Syntax.lbdef
                              in
                           let has_attr =
                             FStar_TypeChecker_Env.fv_has_attr env lbname
                               FStar_Parser_Const.must_erase_for_extraction_attr
                              in
                           (if must_erase && (Prims.op_Negation has_attr)
                            then
                              let uu____1115 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____1116 =
                                let uu____1122 =
                                  let uu____1124 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____1126 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____1124 uu____1126
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____1122)
                                 in
                              FStar_Errors.log_issue uu____1115 uu____1116
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____1133 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____1134 =
                                   let uu____1140 =
                                     let uu____1142 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____1142
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____1140)
                                    in
                                 FStar_Errors.log_issue uu____1133 uu____1134)
                              else ())
                         else ())))
          else ()
      | uu____1152 -> ()
  
let (unembed_optionstate_knot :
  FStar_Options.optionstate FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (unembed_optionstate :
  FStar_Syntax_Syntax.term ->
    FStar_Options.optionstate FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____1182 =
      let uu____1189 =
        let uu____1192 = FStar_ST.op_Bang unembed_optionstate_knot  in
        FStar_Util.must uu____1192  in
      FStar_Syntax_Embeddings.unembed uu____1189 t  in
    uu____1182 true FStar_Syntax_Embeddings.id_norm_cb
  
let proc_check_with :
  'a . FStar_Syntax_Syntax.attribute Prims.list -> (unit -> 'a) -> 'a =
  fun attrs  ->
    fun kont  ->
      let uu____1254 =
        FStar_Syntax_Util.get_attribute FStar_Parser_Const.check_with_lid
          attrs
         in
      match uu____1254 with
      | FStar_Pervasives_Native.None  -> kont ()
      | FStar_Pervasives_Native.Some ((a1,FStar_Pervasives_Native.None )::[])
          ->
          FStar_Options.with_saved_options
            (fun uu____1282  ->
               (let uu____1284 =
                  let uu____1285 = unembed_optionstate a1  in
                  FStar_All.pipe_right uu____1285 FStar_Util.must  in
                FStar_Options.set uu____1284);
               kont ())
      | uu____1290 -> failwith "huh?"
  
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
  fun env0  ->
    fun se  ->
      let env = env0  in
      FStar_TypeChecker_Util.check_sigelt_quals env se;
      proc_check_with se.FStar_Syntax_Syntax.sigattrs
        (fun uu____1402  ->
           let r = se.FStar_Syntax_Syntax.sigrng  in
           let se1 =
             let uu____1405 = FStar_Options.record_options ()  in
             if uu____1405
             then
               let uu___250_1408 = se  in
               let uu____1409 =
                 let uu____1412 = FStar_Options.peek ()  in
                 FStar_Pervasives_Native.Some uu____1412  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (uu___250_1408.FStar_Syntax_Syntax.sigel);
                 FStar_Syntax_Syntax.sigrng =
                   (uu___250_1408.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___250_1408.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___250_1408.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___250_1408.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts = uu____1409
               }
             else se  in
           match se1.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ uu____1425 ->
               failwith "Impossible bare data-constructor"
           | FStar_Syntax_Syntax.Sig_datacon uu____1453 ->
               failwith "Impossible bare data-constructor"
           | FStar_Syntax_Syntax.Sig_fail (uu____1480,false ,uu____1481) when
               (let uu____1496 = FStar_TypeChecker_Env.should_verify env  in
                Prims.op_Negation uu____1496) ||
                 (FStar_Options.admit_smt_queries ())
               -> ([], [], env)
           | FStar_Syntax_Syntax.Sig_fail (expected_errors,lax,ses) ->
               let env' =
                 if lax
                 then
                   let uu___268_1519 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___268_1519.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___268_1519.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___268_1519.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___268_1519.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___268_1519.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___268_1519.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___268_1519.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___268_1519.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___268_1519.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___268_1519.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___268_1519.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___268_1519.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___268_1519.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___268_1519.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___268_1519.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___268_1519.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___268_1519.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.use_eq_strict =
                       (uu___268_1519.FStar_TypeChecker_Env.use_eq_strict);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___268_1519.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___268_1519.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___268_1519.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___268_1519.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___268_1519.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___268_1519.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___268_1519.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___268_1519.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___268_1519.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___268_1519.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___268_1519.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___268_1519.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___268_1519.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___268_1519.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___268_1519.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___268_1519.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___268_1519.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.try_solve_implicits_hook =
                       (uu___268_1519.FStar_TypeChecker_Env.try_solve_implicits_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___268_1519.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.mpreprocess =
                       (uu___268_1519.FStar_TypeChecker_Env.mpreprocess);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___268_1519.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___268_1519.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___268_1519.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___268_1519.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___268_1519.FStar_TypeChecker_Env.nbe);
                     FStar_TypeChecker_Env.strict_args_tab =
                       (uu___268_1519.FStar_TypeChecker_Env.strict_args_tab);
                     FStar_TypeChecker_Env.erasable_types_tab =
                       (uu___268_1519.FStar_TypeChecker_Env.erasable_types_tab)
                   }
                 else env  in
               let env'1 = FStar_TypeChecker_Env.push env' "expect_failure"
                  in
               ((let uu____1526 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Low  in
                 if uu____1526
                 then
                   let uu____1529 =
                     let uu____1531 =
                       FStar_List.map FStar_Util.string_of_int
                         expected_errors
                        in
                     FStar_All.pipe_left (FStar_String.concat "; ")
                       uu____1531
                      in
                   FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____1529
                 else ());
                (let uu____1545 =
                   FStar_Errors.catch_errors
                     (fun uu____1575  ->
                        FStar_Options.with_saved_options
                          (fun uu____1588  ->
                             let uu____1589 =
                               let uu____1610 =
                                 FStar_ST.op_Bang tc_decls_knot  in
                               FStar_Util.must uu____1610  in
                             uu____1589 env'1 ses))
                    in
                 match uu____1545 with
                 | (errs,uu____1719) ->
                     ((let uu____1749 =
                         (FStar_Options.print_expected_failures ()) ||
                           (FStar_TypeChecker_Env.debug env FStar_Options.Low)
                          in
                       if uu____1749
                       then
                         (FStar_Util.print_string ">> Got issues: [\n";
                          FStar_List.iter FStar_Errors.print_issue errs;
                          FStar_Util.print_string ">>]\n")
                       else ());
                      (let uu____1758 =
                         FStar_TypeChecker_Env.pop env'1 "expect_failure"  in
                       let actual_errors =
                         FStar_List.concatMap
                           (fun i  ->
                              FStar_Common.list_of_option
                                i.FStar_Errors.issue_number) errs
                          in
                       (match errs with
                        | [] ->
                            (FStar_List.iter FStar_Errors.print_issue errs;
                             FStar_Errors.log_issue
                               se1.FStar_Syntax_Syntax.sigrng
                               (FStar_Errors.Error_DidNotFail,
                                 "This top-level definition was expected to fail, but it succeeded"))
                        | uu____1772 ->
                            if expected_errors <> []
                            then
                              let uu____1780 =
                                FStar_Errors.find_multiset_discrepancy
                                  expected_errors actual_errors
                                 in
                              (match uu____1780 with
                               | FStar_Pervasives_Native.None  -> ()
                               | FStar_Pervasives_Native.Some (e,n1,n2) ->
                                   (FStar_List.iter FStar_Errors.print_issue
                                      errs;
                                    (let uu____1820 =
                                       let uu____1826 =
                                         let uu____1828 =
                                           FStar_Common.string_of_list
                                             FStar_Util.string_of_int
                                             expected_errors
                                            in
                                         let uu____1831 =
                                           FStar_Common.string_of_list
                                             FStar_Util.string_of_int
                                             actual_errors
                                            in
                                         let uu____1834 =
                                           FStar_Util.string_of_int e  in
                                         let uu____1836 =
                                           FStar_Util.string_of_int n2  in
                                         let uu____1838 =
                                           FStar_Util.string_of_int n1  in
                                         FStar_Util.format5
                                           "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                           uu____1828 uu____1831 uu____1834
                                           uu____1836 uu____1838
                                          in
                                       (FStar_Errors.Error_DidNotFail,
                                         uu____1826)
                                        in
                                     FStar_Errors.log_issue
                                       se1.FStar_Syntax_Syntax.sigrng
                                       uu____1820)))
                            else ());
                       ([], [], env)))))
           | FStar_Syntax_Syntax.Sig_bundle (ses,lids) when
               FStar_All.pipe_right lids
                 (FStar_Util.for_some
                    (FStar_Ident.lid_equals FStar_Parser_Const.lex_t_lid))
               ->
               let env1 = FStar_TypeChecker_Env.set_range env r  in
               let se2 =
                 tc_lex_t env1 ses se1.FStar_Syntax_Syntax.sigquals lids  in
               ([se2], [], env0)
           | FStar_Syntax_Syntax.Sig_bundle (ses,lids) ->
               let env1 = FStar_TypeChecker_Env.set_range env r  in
               let ses1 =
                 let uu____1881 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env1)
                    in
                 if uu____1881
                 then
                   let ses1 =
                     let uu____1889 =
                       let uu____1890 =
                         let uu____1891 =
                           tc_inductive
                             (let uu___310_1900 = env1  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___310_1900.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___310_1900.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___310_1900.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___310_1900.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___310_1900.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___310_1900.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___310_1900.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___310_1900.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___310_1900.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___310_1900.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___310_1900.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___310_1900.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___310_1900.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___310_1900.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___310_1900.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___310_1900.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___310_1900.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (uu___310_1900.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___310_1900.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___310_1900.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___310_1900.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___310_1900.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___310_1900.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___310_1900.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___310_1900.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___310_1900.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___310_1900.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___310_1900.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___310_1900.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___310_1900.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___310_1900.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___310_1900.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___310_1900.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___310_1900.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___310_1900.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___310_1900.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (uu___310_1900.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___310_1900.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___310_1900.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___310_1900.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___310_1900.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___310_1900.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___310_1900.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___310_1900.FStar_TypeChecker_Env.erasable_types_tab)
                              }) ses se1.FStar_Syntax_Syntax.sigquals
                             se1.FStar_Syntax_Syntax.sigattrs lids
                            in
                         FStar_All.pipe_right uu____1891
                           FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____1890
                         (FStar_TypeChecker_Normalize.elim_uvars env1)
                        in
                     FStar_All.pipe_right uu____1889
                       FStar_Syntax_Util.ses_of_sigbundle
                      in
                   ((let uu____1914 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____1914
                     then
                       let uu____1919 =
                         FStar_Syntax_Print.sigelt_to_string
                           (let uu___314_1923 = se1  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                              FStar_Syntax_Syntax.sigrng =
                                (uu___314_1923.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___314_1923.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___314_1923.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___314_1923.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (uu___314_1923.FStar_Syntax_Syntax.sigopts)
                            })
                          in
                       FStar_Util.print1 "Inductive after phase 1: %s\n"
                         uu____1919
                     else ());
                    ses1)
                 else ses  in
               let uu____1933 =
                 tc_inductive env1 ses1 se1.FStar_Syntax_Syntax.sigquals
                   se1.FStar_Syntax_Syntax.sigattrs lids
                  in
               (match uu____1933 with
                | (sigbndle,projectors_ses) ->
                    let sigbndle1 =
                      let uu___321_1957 = sigbndle  in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___321_1957.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___321_1957.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___321_1957.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___321_1957.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (se1.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___321_1957.FStar_Syntax_Syntax.sigopts)
                      }  in
                    ([sigbndle1], projectors_ses, env0))
           | FStar_Syntax_Syntax.Sig_pragma p ->
               (FStar_Syntax_Util.process_pragma p r; ([se1], [], env0))
           | FStar_Syntax_Syntax.Sig_new_effect ne ->
               let is_unelaborated_dm4f =
                 match ne.FStar_Syntax_Syntax.combinators with
                 | FStar_Syntax_Syntax.DM4F_eff combs ->
                     let uu____1973 =
                       let uu____1976 =
                         FStar_All.pipe_right
                           combs.FStar_Syntax_Syntax.ret_wp
                           FStar_Pervasives_Native.snd
                          in
                       FStar_All.pipe_right uu____1976
                         FStar_Syntax_Subst.compress
                        in
                     (match uu____1973 with
                      | {
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_unknown ;
                          FStar_Syntax_Syntax.pos = uu____1992;
                          FStar_Syntax_Syntax.vars = uu____1993;_} -> true
                      | uu____1997 -> false)
                 | uu____2001 -> false  in
               if is_unelaborated_dm4f
               then
                 let uu____2014 =
                   FStar_TypeChecker_TcEffect.dmff_cps_and_elaborate env ne
                    in
                 (match uu____2014 with
                  | (ses,ne1,lift_from_pure_opt) ->
                      let effect_and_lift_ses =
                        match lift_from_pure_opt with
                        | FStar_Pervasives_Native.Some lift ->
                            [(let uu___345_2053 = se1  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___345_2053.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___345_2053.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___345_2053.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___345_2053.FStar_Syntax_Syntax.sigattrs);
                                FStar_Syntax_Syntax.sigopts =
                                  (uu___345_2053.FStar_Syntax_Syntax.sigopts)
                              });
                            lift]
                        | FStar_Pervasives_Native.None  ->
                            [(let uu___348_2055 = se1  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___348_2055.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___348_2055.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___348_2055.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___348_2055.FStar_Syntax_Syntax.sigattrs);
                                FStar_Syntax_Syntax.sigopts =
                                  (uu___348_2055.FStar_Syntax_Syntax.sigopts)
                              })]
                         in
                      ([], (FStar_List.append ses effect_and_lift_ses), env0))
               else
                 (let ne1 =
                    let uu____2063 =
                      (FStar_Options.use_two_phase_tc ()) &&
                        (FStar_TypeChecker_Env.should_verify env)
                       in
                    if uu____2063
                    then
                      let ne1 =
                        let uu____2067 =
                          let uu____2068 =
                            let uu____2069 =
                              FStar_TypeChecker_TcEffect.tc_eff_decl
                                (let uu___352_2072 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___352_2072.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___352_2072.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___352_2072.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___352_2072.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___352_2072.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___352_2072.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___352_2072.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___352_2072.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___352_2072.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___352_2072.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___352_2072.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___352_2072.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___352_2072.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___352_2072.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___352_2072.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___352_2072.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___352_2072.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___352_2072.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___352_2072.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___352_2072.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___352_2072.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 = true;
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___352_2072.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___352_2072.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___352_2072.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___352_2072.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___352_2072.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___352_2072.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___352_2072.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___352_2072.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___352_2072.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___352_2072.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___352_2072.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___352_2072.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___352_2072.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___352_2072.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___352_2072.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___352_2072.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___352_2072.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___352_2072.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___352_2072.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___352_2072.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___352_2072.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___352_2072.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___352_2072.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) ne se1.FStar_Syntax_Syntax.sigquals
                               in
                            FStar_All.pipe_right uu____2069
                              (fun ne1  ->
                                 let uu___355_2078 = se1  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___355_2078.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals =
                                     (uu___355_2078.FStar_Syntax_Syntax.sigquals);
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___355_2078.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___355_2078.FStar_Syntax_Syntax.sigattrs);
                                   FStar_Syntax_Syntax.sigopts =
                                     (uu___355_2078.FStar_Syntax_Syntax.sigopts)
                                 })
                             in
                          FStar_All.pipe_right uu____2068
                            (FStar_TypeChecker_Normalize.elim_uvars env)
                           in
                        FStar_All.pipe_right uu____2067
                          FStar_Syntax_Util.eff_decl_of_new_effect
                         in
                      ((let uu____2080 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "TwoPhases")
                           in
                        if uu____2080
                        then
                          let uu____2085 =
                            FStar_Syntax_Print.sigelt_to_string
                              (let uu___359_2089 = se1  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___359_2089.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals =
                                   (uu___359_2089.FStar_Syntax_Syntax.sigquals);
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___359_2089.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___359_2089.FStar_Syntax_Syntax.sigattrs);
                                 FStar_Syntax_Syntax.sigopts =
                                   (uu___359_2089.FStar_Syntax_Syntax.sigopts)
                               })
                             in
                          FStar_Util.print1 "Effect decl after phase 1: %s\n"
                            uu____2085
                        else ());
                       ne1)
                    else ne  in
                  let ne2 =
                    FStar_TypeChecker_TcEffect.tc_eff_decl env ne1
                      se1.FStar_Syntax_Syntax.sigquals
                     in
                  let se2 =
                    let uu___364_2097 = se1  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_new_effect ne2);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___364_2097.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___364_2097.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___364_2097.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___364_2097.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___364_2097.FStar_Syntax_Syntax.sigopts)
                    }  in
                  ([se2], [], env0))
           | FStar_Syntax_Syntax.Sig_sub_effect sub ->
               let sub1 = FStar_TypeChecker_TcEffect.tc_lift env sub r  in
               let se2 =
                 let uu___370_2105 = se1  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_sub_effect sub1);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___370_2105.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___370_2105.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___370_2105.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___370_2105.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (uu___370_2105.FStar_Syntax_Syntax.sigopts)
                 }  in
               ([se2], [], env)
           | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
               let uu____2119 =
                 let uu____2128 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env)
                    in
                 if uu____2128
                 then
                   let uu____2139 =
                     let uu____2140 =
                       let uu____2141 =
                         FStar_TypeChecker_TcEffect.tc_effect_abbrev
                           (let uu___381_2152 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___381_2152.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___381_2152.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___381_2152.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___381_2152.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___381_2152.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___381_2152.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___381_2152.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___381_2152.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___381_2152.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___381_2152.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___381_2152.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___381_2152.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___381_2152.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___381_2152.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___381_2152.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___381_2152.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___381_2152.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___381_2152.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___381_2152.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___381_2152.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___381_2152.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 = true;
                              FStar_TypeChecker_Env.failhard =
                                (uu___381_2152.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___381_2152.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___381_2152.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___381_2152.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___381_2152.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___381_2152.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___381_2152.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___381_2152.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___381_2152.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___381_2152.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___381_2152.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___381_2152.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___381_2152.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___381_2152.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___381_2152.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___381_2152.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___381_2152.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___381_2152.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___381_2152.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___381_2152.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___381_2152.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___381_2152.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___381_2152.FStar_TypeChecker_Env.erasable_types_tab)
                            }) (lid, uvs, tps, c) r
                          in
                       FStar_All.pipe_right uu____2141
                         (fun uu____2169  ->
                            match uu____2169 with
                            | (lid1,uvs1,tps1,c1) ->
                                let uu___388_2182 = se1  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_effect_abbrev
                                       (lid1, uvs1, tps1, c1, flags));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___388_2182.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___388_2182.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___388_2182.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___388_2182.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___388_2182.FStar_Syntax_Syntax.sigopts)
                                })
                        in
                     FStar_All.pipe_right uu____2140
                       (FStar_TypeChecker_Normalize.elim_uvars env)
                      in
                   FStar_All.pipe_right uu____2139
                     (fun se2  ->
                        match se2.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_effect_abbrev
                            (lid1,uvs1,tps1,c1,uu____2212) ->
                            (lid1, uvs1, tps1, c1)
                        | uu____2217 ->
                            failwith
                              "Did not expect Sig_effect_abbrev to not be one after phase 1")
                 else (lid, uvs, tps, c)  in
               (match uu____2119 with
                | (lid1,uvs1,tps1,c1) ->
                    let uu____2243 =
                      FStar_TypeChecker_TcEffect.tc_effect_abbrev env
                        (lid1, uvs1, tps1, c1) r
                       in
                    (match uu____2243 with
                     | (lid2,uvs2,tps2,c2) ->
                         let se2 =
                           let uu___409_2267 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  (lid2, uvs2, tps2, c2, flags));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___409_2267.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___409_2267.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___409_2267.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___409_2267.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___409_2267.FStar_Syntax_Syntax.sigopts)
                           }  in
                         ([se2], [], env0)))
           | FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2274,uu____2275,uu____2276) when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___0_2281  ->
                       match uu___0_2281 with
                       | FStar_Syntax_Syntax.OnlyName  -> true
                       | uu____2284 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_let (uu____2290,uu____2291) when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___0_2300  ->
                       match uu___0_2300 with
                       | FStar_Syntax_Syntax.OnlyName  -> true
                       | uu____2303 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
               let env1 = FStar_TypeChecker_Env.set_range env r  in
               ((let uu____2314 = FStar_TypeChecker_Env.lid_exists env1 lid
                    in
                 if uu____2314
                 then
                   let uu____2317 =
                     let uu____2323 =
                       let uu____2325 = FStar_Ident.string_of_lid lid  in
                       FStar_Util.format1
                         "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                         uu____2325
                        in
                     (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                       uu____2323)
                      in
                   FStar_Errors.raise_error uu____2317 r
                 else ());
                (let uu____2331 =
                   let uu____2340 =
                     (FStar_Options.use_two_phase_tc ()) &&
                       (FStar_TypeChecker_Env.should_verify env1)
                      in
                   if uu____2340
                   then
                     let uu____2351 =
                       tc_declare_typ
                         (let uu___433_2354 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___433_2354.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___433_2354.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___433_2354.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___433_2354.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___433_2354.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___433_2354.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___433_2354.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___433_2354.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___433_2354.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___433_2354.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___433_2354.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___433_2354.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___433_2354.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___433_2354.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___433_2354.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___433_2354.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___433_2354.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___433_2354.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___433_2354.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___433_2354.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___433_2354.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___433_2354.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___433_2354.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___433_2354.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___433_2354.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___433_2354.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___433_2354.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___433_2354.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___433_2354.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___433_2354.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___433_2354.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___433_2354.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___433_2354.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___433_2354.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___433_2354.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___433_2354.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___433_2354.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___433_2354.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___433_2354.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___433_2354.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___433_2354.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___433_2354.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___433_2354.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___433_2354.FStar_TypeChecker_Env.erasable_types_tab)
                          }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng
                        in
                     match uu____2351 with
                     | (uvs1,t1) ->
                         ((let uu____2380 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "TwoPhases")
                              in
                           if uu____2380
                           then
                             let uu____2385 =
                               FStar_Syntax_Print.term_to_string t1  in
                             let uu____2387 =
                               FStar_Syntax_Print.univ_names_to_string uvs1
                                in
                             FStar_Util.print2
                               "Val declaration after phase 1: %s and uvs: %s\n"
                               uu____2385 uu____2387
                           else ());
                          (uvs1, t1))
                   else (uvs, t)  in
                 match uu____2331 with
                 | (uvs1,t1) ->
                     let uu____2422 =
                       tc_declare_typ env1 (uvs1, t1)
                         se1.FStar_Syntax_Syntax.sigrng
                        in
                     (match uu____2422 with
                      | (uvs2,t2) ->
                          ([(let uu___446_2452 = se1  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (lid, uvs2, t2));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___446_2452.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___446_2452.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___446_2452.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___446_2452.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___446_2452.FStar_Syntax_Syntax.sigopts)
                             })], [], env0))))
           | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
               let env1 = FStar_TypeChecker_Env.set_range env r  in
               let uu____2457 =
                 let uu____2466 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env1)
                    in
                 if uu____2466
                 then
                   let uu____2477 =
                     tc_assume
                       (let uu___455_2480 = env1  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___455_2480.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___455_2480.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___455_2480.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___455_2480.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___455_2480.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___455_2480.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___455_2480.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___455_2480.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___455_2480.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___455_2480.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___455_2480.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___455_2480.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___455_2480.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___455_2480.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level =
                            (uu___455_2480.FStar_TypeChecker_Env.top_level);
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___455_2480.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___455_2480.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.use_eq_strict =
                            (uu___455_2480.FStar_TypeChecker_Env.use_eq_strict);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___455_2480.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___455_2480.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax = true;
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___455_2480.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 = true;
                          FStar_TypeChecker_Env.failhard =
                            (uu___455_2480.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___455_2480.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___455_2480.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___455_2480.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___455_2480.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___455_2480.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___455_2480.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___455_2480.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___455_2480.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___455_2480.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___455_2480.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___455_2480.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___455_2480.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.try_solve_implicits_hook =
                            (uu___455_2480.FStar_TypeChecker_Env.try_solve_implicits_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___455_2480.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.mpreprocess =
                            (uu___455_2480.FStar_TypeChecker_Env.mpreprocess);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___455_2480.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___455_2480.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___455_2480.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___455_2480.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___455_2480.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___455_2480.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (uu___455_2480.FStar_TypeChecker_Env.erasable_types_tab)
                        }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng
                      in
                   match uu____2477 with
                   | (uvs1,t1) ->
                       ((let uu____2506 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "TwoPhases")
                            in
                         if uu____2506
                         then
                           let uu____2511 =
                             FStar_Syntax_Print.term_to_string t1  in
                           let uu____2513 =
                             FStar_Syntax_Print.univ_names_to_string uvs1  in
                           FStar_Util.print2
                             "Assume after phase 1: %s and uvs: %s\n"
                             uu____2511 uu____2513
                         else ());
                        (uvs1, t1))
                 else (uvs, t)  in
               (match uu____2457 with
                | (uvs1,t1) ->
                    let uu____2548 =
                      tc_assume env1 (uvs1, t1)
                        se1.FStar_Syntax_Syntax.sigrng
                       in
                    (match uu____2548 with
                     | (uvs2,t2) ->
                         ([(let uu___468_2578 = se1  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_assume
                                   (lid, uvs2, t2));
                              FStar_Syntax_Syntax.sigrng =
                                (uu___468_2578.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___468_2578.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___468_2578.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___468_2578.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (uu___468_2578.FStar_Syntax_Syntax.sigopts)
                            })], [], env0)))
           | FStar_Syntax_Syntax.Sig_main e ->
               let env1 = FStar_TypeChecker_Env.set_range env r  in
               let env2 =
                 FStar_TypeChecker_Env.set_expected_typ env1
                   FStar_Syntax_Syntax.t_unit
                  in
               let uu____2582 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
               (match uu____2582 with
                | (e1,c,g1) ->
                    let uu____2602 =
                      let uu____2609 = FStar_TypeChecker_Common.lcomp_comp c
                         in
                      match uu____2609 with
                      | (c1,g_lc) ->
                          let uu____2622 =
                            let uu____2629 =
                              let uu____2632 =
                                FStar_Syntax_Util.ml_comp
                                  FStar_Syntax_Syntax.t_unit r
                                 in
                              FStar_Pervasives_Native.Some uu____2632  in
                            FStar_TypeChecker_TcTerm.check_expected_effect
                              env2 uu____2629 (e1, c1)
                             in
                          (match uu____2622 with
                           | (e2,_x,g) ->
                               let uu____2642 =
                                 FStar_TypeChecker_Env.conj_guard g_lc g  in
                               (e2, _x, uu____2642))
                       in
                    (match uu____2602 with
                     | (e2,uu____2654,g) ->
                         ((let uu____2657 =
                             FStar_TypeChecker_Env.conj_guard g1 g  in
                           FStar_TypeChecker_Rel.force_trivial_guard env2
                             uu____2657);
                          (let se2 =
                             let uu___490_2659 = se1  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_main e2);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___490_2659.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___490_2659.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___490_2659.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___490_2659.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___490_2659.FStar_Syntax_Syntax.sigopts)
                             }  in
                           ([se2], [], env0)))))
           | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
               ((let uu____2671 = FStar_Options.debug_any ()  in
                 if uu____2671
                 then
                   let uu____2674 =
                     FStar_Ident.string_of_lid
                       env.FStar_TypeChecker_Env.curmodule
                      in
                   let uu____2676 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print2 "%s: Found splice of (%s)\n" uu____2674
                     uu____2676
                 else ());
                (let uu____2681 =
                   FStar_TypeChecker_TcTerm.tc_tactic
                     FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_decls
                     env t
                    in
                 match uu____2681 with
                 | (t1,uu____2699,g) ->
                     (FStar_TypeChecker_Rel.force_trivial_guard env g;
                      (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                       let lids' =
                         FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                           ses
                          in
                       FStar_List.iter
                         (fun lid  ->
                            let uu____2713 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids'
                               in
                            match uu____2713 with
                            | FStar_Pervasives_Native.None  when
                                Prims.op_Negation
                                  env.FStar_TypeChecker_Env.nosynth
                                ->
                                let uu____2716 =
                                  let uu____2722 =
                                    let uu____2724 =
                                      FStar_Ident.string_of_lid lid  in
                                    let uu____2726 =
                                      let uu____2728 =
                                        FStar_List.map
                                          FStar_Ident.string_of_lid lids'
                                         in
                                      FStar_All.pipe_left
                                        (FStar_String.concat ", ") uu____2728
                                       in
                                    FStar_Util.format2
                                      "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                      uu____2724 uu____2726
                                     in
                                  (FStar_Errors.Fatal_SplicedUndef,
                                    uu____2722)
                                   in
                                FStar_Errors.raise_error uu____2716 r
                            | uu____2740 -> ()) lids;
                       (let dsenv =
                          FStar_List.fold_left
                            FStar_Syntax_DsEnv.push_sigelt_force
                            env.FStar_TypeChecker_Env.dsenv ses
                           in
                        let env1 =
                          let uu___511_2745 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___511_2745.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___511_2745.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___511_2745.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___511_2745.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___511_2745.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___511_2745.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___511_2745.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___511_2745.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___511_2745.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___511_2745.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___511_2745.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___511_2745.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___511_2745.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___511_2745.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___511_2745.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___511_2745.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___511_2745.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___511_2745.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___511_2745.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___511_2745.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___511_2745.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___511_2745.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___511_2745.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___511_2745.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___511_2745.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___511_2745.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___511_2745.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___511_2745.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___511_2745.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___511_2745.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___511_2745.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___511_2745.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___511_2745.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___511_2745.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___511_2745.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___511_2745.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___511_2745.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___511_2745.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___511_2745.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___511_2745.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___511_2745.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___511_2745.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv = dsenv;
                            FStar_TypeChecker_Env.nbe =
                              (uu___511_2745.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___511_2745.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___511_2745.FStar_TypeChecker_Env.erasable_types_tab)
                          }  in
                        ([], ses, env1))))))
           | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
               let env1 = FStar_TypeChecker_Env.set_range env r  in
               let check_quals_eq l qopt val_q =
                 match qopt with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.Some val_q
                 | FStar_Pervasives_Native.Some q' ->
                     let drop_logic =
                       FStar_List.filter
                         (fun x  ->
                            Prims.op_Negation (x = FStar_Syntax_Syntax.Logic))
                        in
                     let uu____2813 =
                       let uu____2815 =
                         let uu____2824 = drop_logic val_q  in
                         let uu____2827 = drop_logic q'  in
                         (uu____2824, uu____2827)  in
                       match uu____2815 with
                       | (val_q1,q'1) ->
                           ((FStar_List.length val_q1) =
                              (FStar_List.length q'1))
                             &&
                             (FStar_List.forall2
                                FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                        in
                     if uu____2813
                     then FStar_Pervasives_Native.Some q'
                     else
                       (let uu____2854 =
                          let uu____2860 =
                            let uu____2862 =
                              FStar_Syntax_Print.lid_to_string l  in
                            let uu____2864 =
                              FStar_Syntax_Print.quals_to_string val_q  in
                            let uu____2866 =
                              FStar_Syntax_Print.quals_to_string q'  in
                            FStar_Util.format3
                              "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                              uu____2862 uu____2864 uu____2866
                             in
                          (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                            uu____2860)
                           in
                        FStar_Errors.raise_error uu____2854 r)
                  in
               let rename_parameters lb =
                 let rename_in_typ def typ =
                   let typ1 = FStar_Syntax_Subst.compress typ  in
                   let def_bs =
                     let uu____2903 =
                       let uu____2904 = FStar_Syntax_Subst.compress def  in
                       uu____2904.FStar_Syntax_Syntax.n  in
                     match uu____2903 with
                     | FStar_Syntax_Syntax.Tm_abs
                         (binders,uu____2916,uu____2917) -> binders
                     | uu____2942 -> []  in
                   match typ1 with
                   | {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                         (val_bs,c);
                       FStar_Syntax_Syntax.pos = r1;
                       FStar_Syntax_Syntax.vars = uu____2954;_} ->
                       let has_auto_name bv =
                         let uu____2984 =
                           FStar_Ident.text_of_id
                             bv.FStar_Syntax_Syntax.ppname
                            in
                         FStar_Util.starts_with uu____2984
                           FStar_Ident.reserved_prefix
                          in
                       let rec rename_binders def_bs1 val_bs1 =
                         match (def_bs1, val_bs1) with
                         | ([],uu____3061) -> val_bs1
                         | (uu____3092,[]) -> val_bs1
                         | ((body_bv,uu____3124)::bt,(val_bv,aqual)::vt) ->
                             let uu____3181 =
                               let uu____3188 =
                                 let uu____3195 = has_auto_name body_bv  in
                                 let uu____3197 = has_auto_name val_bv  in
                                 (uu____3195, uu____3197)  in
                               match uu____3188 with
                               | (true ,uu____3207) -> (val_bv, aqual)
                               | (false ,true ) ->
                                   let uu____3218 =
                                     let uu___580_3219 = val_bv  in
                                     let uu____3220 =
                                       let uu____3221 =
                                         let uu____3227 =
                                           FStar_Ident.text_of_id
                                             body_bv.FStar_Syntax_Syntax.ppname
                                            in
                                         let uu____3229 =
                                           FStar_Ident.range_of_id
                                             val_bv.FStar_Syntax_Syntax.ppname
                                            in
                                         (uu____3227, uu____3229)  in
                                       FStar_Ident.mk_ident uu____3221  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         uu____3220;
                                       FStar_Syntax_Syntax.index =
                                         (uu___580_3219.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (uu___580_3219.FStar_Syntax_Syntax.sort)
                                     }  in
                                   (uu____3218, aqual)
                               | (false ,false ) -> (val_bv, aqual)  in
                             let uu____3239 = rename_binders bt vt  in
                             uu____3181 :: uu____3239
                          in
                       let uu____3254 =
                         let uu____3261 =
                           let uu____3262 =
                             let uu____3277 = rename_binders def_bs val_bs
                                in
                             (uu____3277, c)  in
                           FStar_Syntax_Syntax.Tm_arrow uu____3262  in
                         FStar_Syntax_Syntax.mk uu____3261  in
                       uu____3254 FStar_Pervasives_Native.None r1
                   | uu____3296 -> typ1  in
                 let uu___586_3297 = lb  in
                 let uu____3298 =
                   rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                     lb.FStar_Syntax_Syntax.lbtyp
                    in
                 {
                   FStar_Syntax_Syntax.lbname =
                     (uu___586_3297.FStar_Syntax_Syntax.lbname);
                   FStar_Syntax_Syntax.lbunivs =
                     (uu___586_3297.FStar_Syntax_Syntax.lbunivs);
                   FStar_Syntax_Syntax.lbtyp = uu____3298;
                   FStar_Syntax_Syntax.lbeff =
                     (uu___586_3297.FStar_Syntax_Syntax.lbeff);
                   FStar_Syntax_Syntax.lbdef =
                     (uu___586_3297.FStar_Syntax_Syntax.lbdef);
                   FStar_Syntax_Syntax.lbattrs =
                     (uu___586_3297.FStar_Syntax_Syntax.lbattrs);
                   FStar_Syntax_Syntax.lbpos =
                     (uu___586_3297.FStar_Syntax_Syntax.lbpos)
                 }  in
               let uu____3301 =
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.fold_left
                      (fun uu____3356  ->
                         fun lb  ->
                           match uu____3356 with
                           | (gen,lbs1,quals_opt) ->
                               let lbname =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu____3402 =
                                 let uu____3414 =
                                   FStar_TypeChecker_Env.try_lookup_val_decl
                                     env1
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 match uu____3414 with
                                 | FStar_Pervasives_Native.None  ->
                                     if lb.FStar_Syntax_Syntax.lbunivs <> []
                                     then (false, lb, quals_opt)
                                     else (gen, lb, quals_opt)
                                 | FStar_Pervasives_Native.Some
                                     ((uvs,tval),quals) ->
                                     let quals_opt1 =
                                       check_quals_eq
                                         (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         quals_opt quals
                                        in
                                     let def =
                                       match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                       with
                                       | FStar_Syntax_Syntax.Tm_unknown  ->
                                           lb.FStar_Syntax_Syntax.lbdef
                                       | uu____3494 ->
                                           FStar_Syntax_Syntax.mk
                                             (FStar_Syntax_Syntax.Tm_ascribed
                                                ((lb.FStar_Syntax_Syntax.lbdef),
                                                  ((FStar_Util.Inl
                                                      (lb.FStar_Syntax_Syntax.lbtyp)),
                                                    FStar_Pervasives_Native.None),
                                                  FStar_Pervasives_Native.None))
                                             FStar_Pervasives_Native.None
                                             (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.pos
                                        in
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
                                      (let uu____3541 =
                                         FStar_Syntax_Syntax.mk_lb
                                           ((FStar_Util.Inr lbname), uvs,
                                             FStar_Parser_Const.effect_ALL_lid,
                                             tval, def, [],
                                             (lb.FStar_Syntax_Syntax.lbpos))
                                          in
                                       (false, uu____3541, quals_opt1)))
                                  in
                               (match uu____3402 with
                                | (gen1,lb1,quals_opt1) ->
                                    (gen1, (lb1 :: lbs1), quals_opt1)))
                      (true, [],
                        (if se1.FStar_Syntax_Syntax.sigquals = []
                         then FStar_Pervasives_Native.None
                         else
                           FStar_Pervasives_Native.Some
                             (se1.FStar_Syntax_Syntax.sigquals))))
                  in
               (match uu____3301 with
                | (should_generalize,lbs',quals_opt) ->
                    let quals =
                      match quals_opt with
                      | FStar_Pervasives_Native.None  ->
                          [FStar_Syntax_Syntax.Visible_default]
                      | FStar_Pervasives_Native.Some q ->
                          let uu____3645 =
                            FStar_All.pipe_right q
                              (FStar_Util.for_some
                                 (fun uu___1_3651  ->
                                    match uu___1_3651 with
                                    | FStar_Syntax_Syntax.Irreducible  ->
                                        true
                                    | FStar_Syntax_Syntax.Visible_default  ->
                                        true
                                    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                         -> true
                                    | uu____3656 -> false))
                             in
                          if uu____3645
                          then q
                          else FStar_Syntax_Syntax.Visible_default :: q
                       in
                    let lbs'1 = FStar_List.rev lbs'  in
                    let uu____3666 =
                      let uu____3675 =
                        FStar_Syntax_Util.extract_attr'
                          FStar_Parser_Const.preprocess_with
                          se1.FStar_Syntax_Syntax.sigattrs
                         in
                      match uu____3675 with
                      | FStar_Pervasives_Native.None  ->
                          ((se1.FStar_Syntax_Syntax.sigattrs),
                            FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some
                          (ats,(tau,FStar_Pervasives_Native.None )::[]) ->
                          (ats, (FStar_Pervasives_Native.Some tau))
                      | FStar_Pervasives_Native.Some (ats,args) ->
                          (FStar_Errors.log_issue r
                             (FStar_Errors.Warning_UnrecognizedAttribute,
                               "Ill-formed application of `preprocess_with`");
                           ((se1.FStar_Syntax_Syntax.sigattrs),
                             FStar_Pervasives_Native.None))
                       in
                    (match uu____3666 with
                     | (attrs,pre_tau) ->
                         let se2 =
                           let uu___644_3780 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___644_3780.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___644_3780.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___644_3780.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___644_3780.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs = attrs;
                             FStar_Syntax_Syntax.sigopts =
                               (uu___644_3780.FStar_Syntax_Syntax.sigopts)
                           }  in
                         let preprocess_lb tau lb =
                           let lbdef =
                             FStar_TypeChecker_Env.preprocess env1 tau
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           (let uu____3794 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TwoPhases")
                               in
                            if uu____3794
                            then
                              let uu____3799 =
                                FStar_Syntax_Print.term_to_string lbdef  in
                              FStar_Util.print1 "lb preprocessed into: %s\n"
                                uu____3799
                            else ());
                           (let uu___653_3804 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___653_3804.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___653_3804.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___653_3804.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___653_3804.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___653_3804.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___653_3804.FStar_Syntax_Syntax.lbpos)
                            })
                            in
                         let lbs'2 =
                           match pre_tau with
                           | FStar_Pervasives_Native.Some tau ->
                               FStar_List.map (preprocess_lb tau) lbs'1
                           | FStar_Pervasives_Native.None  -> lbs'1  in
                         let e =
                           let uu____3814 =
                             let uu____3821 =
                               let uu____3822 =
                                 let uu____3836 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_constant
                                        FStar_Const.Const_unit)
                                     FStar_Pervasives_Native.None r
                                    in
                                 (((FStar_Pervasives_Native.fst lbs), lbs'2),
                                   uu____3836)
                                  in
                               FStar_Syntax_Syntax.Tm_let uu____3822  in
                             FStar_Syntax_Syntax.mk uu____3821  in
                           uu____3814 FStar_Pervasives_Native.None r  in
                         let env' =
                           let uu___660_3855 = env1  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___660_3855.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___660_3855.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___660_3855.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___660_3855.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___660_3855.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___660_3855.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___660_3855.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___660_3855.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___660_3855.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___660_3855.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___660_3855.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___660_3855.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               should_generalize;
                             FStar_TypeChecker_Env.letrecs =
                               (uu___660_3855.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = true;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___660_3855.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___660_3855.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___660_3855.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___660_3855.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___660_3855.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___660_3855.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___660_3855.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___660_3855.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___660_3855.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___660_3855.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___660_3855.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___660_3855.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___660_3855.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___660_3855.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___660_3855.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___660_3855.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___660_3855.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___660_3855.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___660_3855.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___660_3855.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___660_3855.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___660_3855.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___660_3855.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___660_3855.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___660_3855.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___660_3855.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___660_3855.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___660_3855.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___660_3855.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___660_3855.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___660_3855.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let e1 =
                           let uu____3858 =
                             (FStar_Options.use_two_phase_tc ()) &&
                               (FStar_TypeChecker_Env.should_verify env')
                              in
                           if uu____3858
                           then
                             let drop_lbtyp e_lax =
                               let uu____3867 =
                                 let uu____3868 =
                                   FStar_Syntax_Subst.compress e_lax  in
                                 uu____3868.FStar_Syntax_Syntax.n  in
                               match uu____3867 with
                               | FStar_Syntax_Syntax.Tm_let
                                   ((false ,lb::[]),e2) ->
                                   let lb_unannotated =
                                     let uu____3890 =
                                       let uu____3891 =
                                         FStar_Syntax_Subst.compress e  in
                                       uu____3891.FStar_Syntax_Syntax.n  in
                                     match uu____3890 with
                                     | FStar_Syntax_Syntax.Tm_let
                                         ((uu____3895,lb1::[]),uu____3897) ->
                                         let uu____3913 =
                                           let uu____3914 =
                                             FStar_Syntax_Subst.compress
                                               lb1.FStar_Syntax_Syntax.lbtyp
                                              in
                                           uu____3914.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____3913 with
                                          | FStar_Syntax_Syntax.Tm_unknown 
                                              -> true
                                          | uu____3919 -> false)
                                     | uu____3921 ->
                                         failwith
                                           "Impossible: first phase lb and second phase lb differ in structure!"
                                      in
                                   if lb_unannotated
                                   then
                                     let uu___685_3925 = e_lax  in
                                     {
                                       FStar_Syntax_Syntax.n =
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((false,
                                               [(let uu___687_3940 = lb  in
                                                 {
                                                   FStar_Syntax_Syntax.lbname
                                                     =
                                                     (uu___687_3940.FStar_Syntax_Syntax.lbname);
                                                   FStar_Syntax_Syntax.lbunivs
                                                     =
                                                     (uu___687_3940.FStar_Syntax_Syntax.lbunivs);
                                                   FStar_Syntax_Syntax.lbtyp
                                                     =
                                                     FStar_Syntax_Syntax.tun;
                                                   FStar_Syntax_Syntax.lbeff
                                                     =
                                                     (uu___687_3940.FStar_Syntax_Syntax.lbeff);
                                                   FStar_Syntax_Syntax.lbdef
                                                     =
                                                     (uu___687_3940.FStar_Syntax_Syntax.lbdef);
                                                   FStar_Syntax_Syntax.lbattrs
                                                     =
                                                     (uu___687_3940.FStar_Syntax_Syntax.lbattrs);
                                                   FStar_Syntax_Syntax.lbpos
                                                     =
                                                     (uu___687_3940.FStar_Syntax_Syntax.lbpos)
                                                 })]), e2));
                                       FStar_Syntax_Syntax.pos =
                                         (uu___685_3925.FStar_Syntax_Syntax.pos);
                                       FStar_Syntax_Syntax.vars =
                                         (uu___685_3925.FStar_Syntax_Syntax.vars)
                                     }
                                   else e_lax
                               | uu____3943 -> e_lax  in
                             let uu____3944 =
                               FStar_Util.record_time
                                 (fun uu____3952  ->
                                    let uu____3953 =
                                      let uu____3954 =
                                        let uu____3955 =
                                          FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                            (let uu___691_3964 = env'  in
                                             {
                                               FStar_TypeChecker_Env.solver =
                                                 (uu___691_3964.FStar_TypeChecker_Env.solver);
                                               FStar_TypeChecker_Env.range =
                                                 (uu___691_3964.FStar_TypeChecker_Env.range);
                                               FStar_TypeChecker_Env.curmodule
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.curmodule);
                                               FStar_TypeChecker_Env.gamma =
                                                 (uu___691_3964.FStar_TypeChecker_Env.gamma);
                                               FStar_TypeChecker_Env.gamma_sig
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.gamma_sig);
                                               FStar_TypeChecker_Env.gamma_cache
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.gamma_cache);
                                               FStar_TypeChecker_Env.modules
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.modules);
                                               FStar_TypeChecker_Env.expected_typ
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.expected_typ);
                                               FStar_TypeChecker_Env.sigtab =
                                                 (uu___691_3964.FStar_TypeChecker_Env.sigtab);
                                               FStar_TypeChecker_Env.attrtab
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.attrtab);
                                               FStar_TypeChecker_Env.instantiate_imp
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.instantiate_imp);
                                               FStar_TypeChecker_Env.effects
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.effects);
                                               FStar_TypeChecker_Env.generalize
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.generalize);
                                               FStar_TypeChecker_Env.letrecs
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.letrecs);
                                               FStar_TypeChecker_Env.top_level
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.top_level);
                                               FStar_TypeChecker_Env.check_uvars
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.check_uvars);
                                               FStar_TypeChecker_Env.use_eq =
                                                 (uu___691_3964.FStar_TypeChecker_Env.use_eq);
                                               FStar_TypeChecker_Env.use_eq_strict
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.use_eq_strict);
                                               FStar_TypeChecker_Env.is_iface
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.is_iface);
                                               FStar_TypeChecker_Env.admit =
                                                 (uu___691_3964.FStar_TypeChecker_Env.admit);
                                               FStar_TypeChecker_Env.lax =
                                                 true;
                                               FStar_TypeChecker_Env.lax_universes
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.lax_universes);
                                               FStar_TypeChecker_Env.phase1 =
                                                 true;
                                               FStar_TypeChecker_Env.failhard
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.failhard);
                                               FStar_TypeChecker_Env.nosynth
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.nosynth);
                                               FStar_TypeChecker_Env.uvar_subtyping
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.uvar_subtyping);
                                               FStar_TypeChecker_Env.tc_term
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.tc_term);
                                               FStar_TypeChecker_Env.type_of
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.type_of);
                                               FStar_TypeChecker_Env.universe_of
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.universe_of);
                                               FStar_TypeChecker_Env.check_type_of
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.check_type_of);
                                               FStar_TypeChecker_Env.use_bv_sorts
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.use_bv_sorts);
                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.qtbl_name_and_index);
                                               FStar_TypeChecker_Env.normalized_eff_names
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.normalized_eff_names);
                                               FStar_TypeChecker_Env.fv_delta_depths
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.fv_delta_depths);
                                               FStar_TypeChecker_Env.proof_ns
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.proof_ns);
                                               FStar_TypeChecker_Env.synth_hook
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.synth_hook);
                                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                               FStar_TypeChecker_Env.splice =
                                                 (uu___691_3964.FStar_TypeChecker_Env.splice);
                                               FStar_TypeChecker_Env.mpreprocess
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.mpreprocess);
                                               FStar_TypeChecker_Env.postprocess
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.postprocess);
                                               FStar_TypeChecker_Env.identifier_info
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.identifier_info);
                                               FStar_TypeChecker_Env.tc_hooks
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.tc_hooks);
                                               FStar_TypeChecker_Env.dsenv =
                                                 (uu___691_3964.FStar_TypeChecker_Env.dsenv);
                                               FStar_TypeChecker_Env.nbe =
                                                 (uu___691_3964.FStar_TypeChecker_Env.nbe);
                                               FStar_TypeChecker_Env.strict_args_tab
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.strict_args_tab);
                                               FStar_TypeChecker_Env.erasable_types_tab
                                                 =
                                                 (uu___691_3964.FStar_TypeChecker_Env.erasable_types_tab)
                                             }) e
                                           in
                                        FStar_All.pipe_right uu____3955
                                          (fun uu____3977  ->
                                             match uu____3977 with
                                             | (e1,uu____3985,uu____3986) ->
                                                 e1)
                                         in
                                      FStar_All.pipe_right uu____3954
                                        (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                           env')
                                       in
                                    FStar_All.pipe_right uu____3953
                                      drop_lbtyp)
                                in
                             match uu____3944 with
                             | (e1,ms) ->
                                 ((let uu____3992 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env1)
                                       (FStar_Options.Other "TwoPhases")
                                      in
                                   if uu____3992
                                   then
                                     let uu____3997 =
                                       FStar_Syntax_Print.term_to_string e1
                                        in
                                     FStar_Util.print1
                                       "Let binding after phase 1: %s\n"
                                       uu____3997
                                   else ());
                                  (let uu____4003 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env1)
                                       (FStar_Options.Other "TCDeclTime")
                                      in
                                   if uu____4003
                                   then
                                     let uu____4008 =
                                       FStar_Util.string_of_int ms  in
                                     FStar_Util.print1
                                       "Let binding elaborated (phase 1) in %s milliseconds\n"
                                       uu____4008
                                   else ());
                                  e1)
                           else e  in
                         let uu____4015 =
                           let uu____4024 =
                             FStar_Syntax_Util.extract_attr'
                               FStar_Parser_Const.postprocess_with
                               se2.FStar_Syntax_Syntax.sigattrs
                              in
                           match uu____4024 with
                           | FStar_Pervasives_Native.None  ->
                               ((se2.FStar_Syntax_Syntax.sigattrs),
                                 FStar_Pervasives_Native.None)
                           | FStar_Pervasives_Native.Some
                               (ats,(tau,FStar_Pervasives_Native.None )::[])
                               -> (ats, (FStar_Pervasives_Native.Some tau))
                           | FStar_Pervasives_Native.Some (ats,args) ->
                               (FStar_Errors.log_issue r
                                  (FStar_Errors.Warning_UnrecognizedAttribute,
                                    "Ill-formed application of `postprocess_with`");
                                ((se2.FStar_Syntax_Syntax.sigattrs),
                                  FStar_Pervasives_Native.None))
                            in
                         (match uu____4015 with
                          | (attrs1,post_tau) ->
                              let se3 =
                                let uu___721_4129 = se2  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___721_4129.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___721_4129.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___721_4129.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___721_4129.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs = attrs1;
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___721_4129.FStar_Syntax_Syntax.sigopts)
                                }  in
                              let postprocess_lb tau lb =
                                let lbdef =
                                  FStar_TypeChecker_Env.postprocess env1 tau
                                    lb.FStar_Syntax_Syntax.lbtyp
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                let uu___728_4142 = lb  in
                                {
                                  FStar_Syntax_Syntax.lbname =
                                    (uu___728_4142.FStar_Syntax_Syntax.lbname);
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___728_4142.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp =
                                    (uu___728_4142.FStar_Syntax_Syntax.lbtyp);
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___728_4142.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = lbdef;
                                  FStar_Syntax_Syntax.lbattrs =
                                    (uu___728_4142.FStar_Syntax_Syntax.lbattrs);
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___728_4142.FStar_Syntax_Syntax.lbpos)
                                }  in
                              let uu____4143 =
                                FStar_Util.record_time
                                  (fun uu____4162  ->
                                     FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                       env' e1)
                                 in
                              (match uu____4143 with
                               | (r1,ms) ->
                                   ((let uu____4190 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "TCDeclTime")
                                        in
                                     if uu____4190
                                     then
                                       let uu____4195 =
                                         FStar_Util.string_of_int ms  in
                                       FStar_Util.print1
                                         "Let binding typechecked in phase 2 in %s milliseconds\n"
                                         uu____4195
                                     else ());
                                    (let uu____4200 =
                                       match r1 with
                                       | ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_let
                                              (lbs1,e2);
                                            FStar_Syntax_Syntax.pos =
                                              uu____4225;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4226;_},uu____4227,g)
                                           when
                                           FStar_TypeChecker_Env.is_trivial g
                                           ->
                                           let lbs2 =
                                             let uu____4257 =
                                               FStar_All.pipe_right
                                                 (FStar_Pervasives_Native.snd
                                                    lbs1)
                                                 (FStar_List.map
                                                    rename_parameters)
                                                in
                                             ((FStar_Pervasives_Native.fst
                                                 lbs1), uu____4257)
                                              in
                                           let lbs3 =
                                             let uu____4281 =
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
                                                     lbs2
                                                in
                                             ((FStar_Pervasives_Native.fst
                                                 lbs2), uu____4281)
                                              in
                                           let quals1 =
                                             match e2.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_meta
                                                 (uu____4304,FStar_Syntax_Syntax.Meta_desugared
                                                  (FStar_Syntax_Syntax.Masked_effect
                                                  ))
                                                 ->
                                                 FStar_Syntax_Syntax.HasMaskedEffect
                                                 :: quals
                                             | uu____4309 -> quals  in
                                           ((let uu___758_4318 = se3  in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_let
                                                    (lbs3, lids));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___758_4318.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 quals1;
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___758_4318.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___758_4318.FStar_Syntax_Syntax.sigattrs);
                                               FStar_Syntax_Syntax.sigopts =
                                                 (uu___758_4318.FStar_Syntax_Syntax.sigopts)
                                             }), lbs3)
                                       | uu____4321 ->
                                           failwith
                                             "impossible (typechecking should preserve Tm_let)"
                                        in
                                     match uu____4200 with
                                     | (se4,lbs1) ->
                                         (FStar_All.pipe_right
                                            (FStar_Pervasives_Native.snd lbs1)
                                            (FStar_List.iter
                                               (fun lb  ->
                                                  let fv =
                                                    FStar_Util.right
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  FStar_TypeChecker_Env.insert_fv_info
                                                    env1 fv
                                                    lb.FStar_Syntax_Syntax.lbtyp));
                                          (let uu____4377 = log env1  in
                                           if uu____4377
                                           then
                                             let uu____4380 =
                                               let uu____4382 =
                                                 FStar_All.pipe_right
                                                   (FStar_Pervasives_Native.snd
                                                      lbs1)
                                                   (FStar_List.map
                                                      (fun lb  ->
                                                         let should_log =
                                                           let uu____4402 =
                                                             let uu____4411 =
                                                               let uu____4412
                                                                 =
                                                                 let uu____4415
                                                                   =
                                                                   FStar_Util.right
                                                                    lb.FStar_Syntax_Syntax.lbname
                                                                    in
                                                                 uu____4415.FStar_Syntax_Syntax.fv_name
                                                                  in
                                                               uu____4412.FStar_Syntax_Syntax.v
                                                                in
                                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                                               env1
                                                               uu____4411
                                                              in
                                                           match uu____4402
                                                           with
                                                           | FStar_Pervasives_Native.None
                                                                -> true
                                                           | uu____4424 ->
                                                               false
                                                            in
                                                         if should_log
                                                         then
                                                           let uu____4436 =
                                                             FStar_Syntax_Print.lbname_to_string
                                                               lb.FStar_Syntax_Syntax.lbname
                                                              in
                                                           let uu____4438 =
                                                             FStar_Syntax_Print.term_to_string
                                                               lb.FStar_Syntax_Syntax.lbtyp
                                                              in
                                                           FStar_Util.format2
                                                             "let %s : %s"
                                                             uu____4436
                                                             uu____4438
                                                         else ""))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____4382
                                                 (FStar_String.concat "\n")
                                                in
                                             FStar_Util.print1 "%s\n"
                                               uu____4380
                                           else ());
                                          check_must_erase_attribute env0 se4;
                                          ([se4], [], env0))))))))
           | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n,p,t,uu____4461) ->
               let t1 =
                 let uu____4463 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env)
                    in
                 if uu____4463
                 then
                   let uu____4466 =
                     let uu____4471 =
                       let uu____4472 =
                         let uu____4473 =
                           FStar_TypeChecker_TcEffect.tc_polymonadic_bind
                             (let uu___783_4480 = env  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___783_4480.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___783_4480.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___783_4480.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___783_4480.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___783_4480.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___783_4480.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___783_4480.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___783_4480.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___783_4480.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___783_4480.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___783_4480.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___783_4480.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___783_4480.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___783_4480.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___783_4480.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___783_4480.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___783_4480.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (uu___783_4480.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___783_4480.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___783_4480.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___783_4480.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___783_4480.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___783_4480.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___783_4480.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___783_4480.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___783_4480.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___783_4480.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___783_4480.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___783_4480.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___783_4480.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___783_4480.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___783_4480.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___783_4480.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___783_4480.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___783_4480.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___783_4480.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (uu___783_4480.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___783_4480.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___783_4480.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___783_4480.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___783_4480.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___783_4480.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___783_4480.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___783_4480.FStar_TypeChecker_Env.erasable_types_tab)
                              }) m n p t
                            in
                         FStar_All.pipe_right uu____4473
                           (fun uu____4491  ->
                              match uu____4491 with
                              | (t1,ty) ->
                                  let uu___788_4498 = se1  in
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (FStar_Syntax_Syntax.Sig_polymonadic_bind
                                         (m, n, p, t1, ty));
                                    FStar_Syntax_Syntax.sigrng =
                                      (uu___788_4498.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals =
                                      (uu___788_4498.FStar_Syntax_Syntax.sigquals);
                                    FStar_Syntax_Syntax.sigmeta =
                                      (uu___788_4498.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (uu___788_4498.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (uu___788_4498.FStar_Syntax_Syntax.sigopts)
                                  })
                          in
                       FStar_All.pipe_right uu____4472
                         (FStar_TypeChecker_Normalize.elim_uvars env)
                        in
                     FStar_All.pipe_right uu____4471
                       (fun se2  ->
                          match se2.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_polymonadic_bind
                              (uu____4514,uu____4515,uu____4516,t1,ty) ->
                              (t1, ty)
                          | uu____4519 ->
                              failwith
                                "Impossible! tc for Sig_polymonadic_bind must be a Sig_polymonadic_bind")
                      in
                   match uu____4466 with
                   | (t1,ty) ->
                       ((let uu____4528 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "TwoPhases")
                            in
                         if uu____4528
                         then
                           let uu____4533 =
                             FStar_Syntax_Print.sigelt_to_string
                               (let uu___803_4537 = se1  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_polymonadic_bind
                                       (m, n, p, t1, ty));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___803_4537.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___803_4537.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___803_4537.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___803_4537.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___803_4537.FStar_Syntax_Syntax.sigopts)
                                })
                              in
                           FStar_Util.print1
                             "Polymonadic bind after phase 1: %s\n"
                             uu____4533
                         else ());
                        t1)
                 else t  in
               let uu____4543 =
                 FStar_TypeChecker_TcEffect.tc_polymonadic_bind env m n p t1
                  in
               (match uu____4543 with
                | (t2,ty) ->
                    let se2 =
                      let uu___810_4561 = se1  in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_polymonadic_bind
                             (m, n, p, t2, ty));
                        FStar_Syntax_Syntax.sigrng =
                          (uu___810_4561.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___810_4561.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___810_4561.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___810_4561.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___810_4561.FStar_Syntax_Syntax.sigopts)
                      }  in
                    ([se2], [], env0)))
  
let (tc_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun se  ->
      let uu____4597 =
        env.FStar_TypeChecker_Env.nosynth && (FStar_Options.debug_any ())  in
      if uu____4597
      then ([], [], env)
      else
        (let env1 = set_hint_correlator env se  in
         (let uu____4618 =
            let uu____4620 =
              FStar_Ident.string_of_lid env1.FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____4620  in
          if uu____4618
          then
            let uu____4623 =
              let uu____4625 =
                FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                  (FStar_List.map FStar_Ident.string_of_lid)
                 in
              FStar_All.pipe_right uu____4625 (FStar_String.concat ", ")  in
            FStar_Util.print1 "Processing %s\n" uu____4623
          else ());
         (let uu____4644 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
             in
          if uu____4644
          then
            let uu____4647 = FStar_Syntax_Print.sigelt_to_string se  in
            FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____4647
          else ());
         tc_decl' env1 se)
  
let for_export :
  'uuuuuu4661 .
    'uuuuuu4661 ->
      FStar_Ident.lident Prims.list ->
        FStar_Syntax_Syntax.sigelt ->
          (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident
            Prims.list)
  =
  fun env  ->
    fun hidden  ->
      fun se  ->
        let is_abstract quals =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___2_4704  ->
                  match uu___2_4704 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____4707 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____4718) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____4726 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____4736 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_fail uu____4741 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_splice uu____4763 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____4779 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____4805 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4831) ->
            let uu____4840 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____4840
            then
              let for_export_bundle se1 uu____4877 =
                match uu____4877 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____4916,uu____4917) ->
                         let dec =
                           let uu___865_4927 = se1  in
                           let uu____4928 =
                             let uu____4929 =
                               let uu____4936 =
                                 let uu____4937 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____4937  in
                               (l, us, uu____4936)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____4929
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____4928;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___865_4927.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___865_4927.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___865_4927.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___865_4927.FStar_Syntax_Syntax.sigopts)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____4947,uu____4948,uu____4949) ->
                         let dec =
                           let uu___876_4957 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___876_4957.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___876_4957.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___876_4957.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___876_4957.FStar_Syntax_Syntax.sigopts)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____4962 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume (uu____4985,uu____4986,uu____4987)
            ->
            let uu____4988 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____4988 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____5012 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____5012
            then
              ([(let uu___892_5031 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___892_5031.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___892_5031.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___892_5031.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (uu___892_5031.FStar_Syntax_Syntax.sigopts)
                 })], (l :: hidden))
            else
              (let uu____5034 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___3_5040  ->
                         match uu___3_5040 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____5043 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____5049 ->
                             true
                         | uu____5051 -> false))
                  in
               if uu____5034 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____5072 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____5077 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____5082 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____5087 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5104 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____5120) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____5134 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____5134
            then ([], hidden)
            else
              (let dec =
                 let uu____5155 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____5155;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = [];
                   FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____5166 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____5166
            then
              let uu____5177 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___929_5191 = se  in
                        let uu____5192 =
                          let uu____5193 =
                            let uu____5200 =
                              let uu____5201 =
                                let uu____5204 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____5204.FStar_Syntax_Syntax.fv_name  in
                              uu____5201.FStar_Syntax_Syntax.v  in
                            (uu____5200, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____5193  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____5192;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___929_5191.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___929_5191.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___929_5191.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___929_5191.FStar_Syntax_Syntax.sigopts)
                        }))
                 in
              (uu____5177, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> Prims.bool -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      fun from_cache  ->
        (let uu____5234 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____5234
         then
           let uu____5237 = FStar_Syntax_Print.sigelt_to_string se  in
           let uu____5239 = FStar_Util.string_of_bool from_cache  in
           FStar_Util.print2
             ">>>>>>>>>>>>>>Adding top-level decl to environment: %s (from_cache:%s)\n"
             uu____5237 uu____5239
         else ());
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____5244 ->
             let uu____5261 =
               let uu____5267 =
                 let uu____5269 = FStar_Syntax_Print.sigelt_to_string se  in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____5269
                  in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____5267)  in
             FStar_Errors.raise_error uu____5261
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_datacon uu____5273 ->
             let uu____5289 =
               let uu____5295 =
                 let uu____5297 = FStar_Syntax_Print.sigelt_to_string se  in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____5297
                  in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____5295)  in
             FStar_Errors.raise_error uu____5289
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_declare_typ
             (uu____5301,uu____5302,uu____5303) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___4_5308  ->
                     match uu___4_5308 with
                     | FStar_Syntax_Syntax.OnlyName  -> true
                     | uu____5311 -> false))
             -> env
         | FStar_Syntax_Syntax.Sig_let (uu____5313,uu____5314) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___4_5323  ->
                     match uu___4_5323 with
                     | FStar_Syntax_Syntax.OnlyName  -> true
                     | uu____5326 -> false))
             -> env
         | uu____5328 ->
             let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PushOptions uu____5330) ->
                  if from_cache
                  then env1
                  else
                    (let uu___966_5337 = env1  in
                     let uu____5338 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___966_5337.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___966_5337.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___966_5337.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___966_5337.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___966_5337.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___966_5337.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___966_5337.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___966_5337.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___966_5337.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___966_5337.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___966_5337.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___966_5337.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___966_5337.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___966_5337.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___966_5337.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___966_5337.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___966_5337.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___966_5337.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___966_5337.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___966_5337.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___966_5337.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___966_5337.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___966_5337.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___966_5337.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___966_5337.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___966_5337.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___966_5337.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___966_5337.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___966_5337.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___966_5337.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___966_5337.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___966_5337.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___966_5337.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___966_5337.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5338;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___966_5337.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___966_5337.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___966_5337.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___966_5337.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___966_5337.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___966_5337.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___966_5337.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___966_5337.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___966_5337.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___966_5337.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___966_5337.FStar_TypeChecker_Env.erasable_types_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PopOptions ) ->
                  if from_cache
                  then env1
                  else
                    (let uu___966_5342 = env1  in
                     let uu____5343 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___966_5342.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___966_5342.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___966_5342.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___966_5342.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___966_5342.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___966_5342.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___966_5342.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___966_5342.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___966_5342.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___966_5342.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___966_5342.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___966_5342.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___966_5342.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___966_5342.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___966_5342.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___966_5342.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___966_5342.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___966_5342.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___966_5342.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___966_5342.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___966_5342.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___966_5342.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___966_5342.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___966_5342.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___966_5342.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___966_5342.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___966_5342.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___966_5342.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___966_5342.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___966_5342.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___966_5342.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___966_5342.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___966_5342.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___966_5342.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5343;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___966_5342.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___966_5342.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___966_5342.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___966_5342.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___966_5342.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___966_5342.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___966_5342.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___966_5342.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___966_5342.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___966_5342.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___966_5342.FStar_TypeChecker_Env.erasable_types_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.SetOptions uu____5344) ->
                  if from_cache
                  then env1
                  else
                    (let uu___966_5349 = env1  in
                     let uu____5350 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___966_5349.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___966_5349.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___966_5349.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___966_5349.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___966_5349.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___966_5349.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___966_5349.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___966_5349.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___966_5349.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___966_5349.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___966_5349.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___966_5349.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___966_5349.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___966_5349.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___966_5349.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___966_5349.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___966_5349.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___966_5349.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___966_5349.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___966_5349.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___966_5349.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___966_5349.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___966_5349.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___966_5349.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___966_5349.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___966_5349.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___966_5349.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___966_5349.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___966_5349.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___966_5349.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___966_5349.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___966_5349.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___966_5349.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___966_5349.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5350;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___966_5349.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___966_5349.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___966_5349.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___966_5349.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___966_5349.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___966_5349.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___966_5349.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___966_5349.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___966_5349.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___966_5349.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___966_5349.FStar_TypeChecker_Env.erasable_types_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.ResetOptions uu____5351) ->
                  if from_cache
                  then env1
                  else
                    (let uu___966_5358 = env1  in
                     let uu____5359 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___966_5358.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___966_5358.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___966_5358.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___966_5358.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___966_5358.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___966_5358.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___966_5358.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___966_5358.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___966_5358.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___966_5358.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___966_5358.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___966_5358.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___966_5358.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___966_5358.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___966_5358.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___966_5358.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___966_5358.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___966_5358.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___966_5358.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___966_5358.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___966_5358.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___966_5358.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___966_5358.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___966_5358.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___966_5358.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___966_5358.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___966_5358.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___966_5358.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___966_5358.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___966_5358.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___966_5358.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___966_5358.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___966_5358.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___966_5358.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5359;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___966_5358.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___966_5358.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___966_5358.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___966_5358.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___966_5358.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___966_5358.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___966_5358.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___966_5358.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___966_5358.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___966_5358.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___966_5358.FStar_TypeChecker_Env.erasable_types_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.RestartSolver ) ->
                  if from_cache || env1.FStar_TypeChecker_Env.nosynth
                  then env1
                  else
                    ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                       ();
                     env1)
              | FStar_Syntax_Syntax.Sig_new_effect ne ->
                  let env2 =
                    FStar_TypeChecker_Env.push_new_effect env1
                      (ne, (se.FStar_Syntax_Syntax.sigquals))
                     in
                  FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
                    (FStar_List.fold_left
                       (fun env3  ->
                          fun a  ->
                            let uu____5375 =
                              FStar_Syntax_Util.action_as_lb
                                ne.FStar_Syntax_Syntax.mname a
                                (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Env.push_sigelt env3 uu____5375)
                       env2)
              | FStar_Syntax_Syntax.Sig_sub_effect sub ->
                  FStar_TypeChecker_Util.update_env_sub_eff env1 sub
              | FStar_Syntax_Syntax.Sig_polymonadic_bind
                  (m,n,p,uu____5380,ty) ->
                  FStar_TypeChecker_Util.update_env_polymonadic_bind env1 m n
                    p ty
              | uu____5382 -> env1))
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____5451 se =
        match uu____5451 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____5504 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____5504
              then
                let uu____5507 = FStar_Syntax_Print.tag_of_sigelt se  in
                let uu____5509 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print2
                  ">>>>>>>>>>>>>>Checking top-level %s decl %s\n" uu____5507
                  uu____5509
              else ());
             (let uu____5514 = tc_decl env1 se  in
              match uu____5514 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____5567 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____5567
                             then
                               let uu____5571 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____5571
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____5587 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____5587
                             then
                               let uu____5591 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\n"
                                 uu____5591
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  (FStar_TypeChecker_Env.promote_id_info env2
                     (fun t  ->
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
                           (fun env3  ->
                              fun se1  -> add_sigelt_to_env env3 se1 false)
                           env2)
                       in
                    FStar_Syntax_Unionfind.reset ();
                    (let uu____5609 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____5609
                     then
                       let uu____5614 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____5623 =
                                  let uu____5625 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____5625 "\n"  in
                                Prims.op_Hat s uu____5623) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____5614
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____5635 =
                       let uu____5644 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____5644
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____5686 se1 =
                            match uu____5686 with
                            | (exports1,hidden1) ->
                                let uu____5714 = for_export env3 hidden1 se1
                                   in
                                (match uu____5714 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____5635 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____5868 = acc  in
        match uu____5868 with
        | (uu____5903,uu____5904,env1,uu____5906) ->
            let r =
              let uu____5940 =
                let uu____5944 =
                  let uu____5946 = FStar_TypeChecker_Env.current_module env1
                     in
                  FStar_Ident.string_of_lid uu____5946  in
                FStar_Pervasives_Native.Some uu____5944  in
              FStar_Profiling.profile
                (fun uu____5969  -> process_one_decl acc se) uu____5940
                "FStar.TypeChecker.Tc.process_one_decl"
               in
            ((let uu____5972 = FStar_Options.profile_group_by_decls ()  in
              if uu____5972
              then
                let tag =
                  match FStar_Syntax_Util.lids_of_sigelt se with
                  | hd::uu____5979 -> FStar_Ident.string_of_lid hd
                  | uu____5982 ->
                      FStar_Range.string_of_range
                        (FStar_Syntax_Util.range_of_sigelt se)
                   in
                FStar_Profiling.report_and_clear tag
              else ());
             r)
         in
      let uu____5987 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____5987 with
      | (ses1,exports,env1,uu____6035) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
  
let (uu___1056 : unit) =
  FStar_ST.op_Colon_Equals tc_decls_knot
    (FStar_Pervasives_Native.Some tc_decls)
  
let (check_exports :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> unit)
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env1 =
          let uu___1060_6151 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1060_6151.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1060_6151.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1060_6151.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1060_6151.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1060_6151.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1060_6151.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1060_6151.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1060_6151.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1060_6151.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1060_6151.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1060_6151.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1060_6151.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1060_6151.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1060_6151.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___1060_6151.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1060_6151.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1060_6151.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1060_6151.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1060_6151.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___1060_6151.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1060_6151.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1060_6151.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1060_6151.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1060_6151.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1060_6151.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1060_6151.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1060_6151.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1060_6151.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1060_6151.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1060_6151.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1060_6151.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1060_6151.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1060_6151.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1060_6151.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1060_6151.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1060_6151.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1060_6151.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1060_6151.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1060_6151.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1060_6151.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1060_6151.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1060_6151.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1060_6151.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        let check_term lid univs t =
          let uu____6171 = FStar_Syntax_Subst.open_univ_vars univs t  in
          match uu____6171 with
          | (univs1,t1) ->
              ((let uu____6179 =
                  let uu____6181 =
                    let uu____6187 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____6187  in
                  FStar_All.pipe_left uu____6181
                    (FStar_Options.Other "Exports")
                   in
                if uu____6179
                then
                  let uu____6191 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____6193 =
                    let uu____6195 =
                      FStar_All.pipe_right univs1
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____6195
                      (FStar_String.concat ", ")
                     in
                  let uu____6212 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____6191 uu____6193 uu____6212
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs1
                   in
                let uu____6218 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____6218 (fun uu____6227  -> ())))
           in
        let check_term1 lid univs t =
          (let uu____6245 =
             let uu____6247 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____6249 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____6247 uu____6249
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____6245);
          check_term lid univs t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6260) ->
              let uu____6269 =
                let uu____6271 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6271  in
              if uu____6269
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs,binders,typ,uu____6285,uu____6286) ->
              let t =
                let uu____6298 =
                  let uu____6305 =
                    let uu____6306 =
                      let uu____6321 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____6321)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____6306  in
                  FStar_Syntax_Syntax.mk uu____6305  in
                uu____6298 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs,t,uu____6337,uu____6338,uu____6339) ->
              check_term1 l univs t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs,t) ->
              let uu____6349 =
                let uu____6351 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6351  in
              if uu____6349 then check_term1 l univs t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____6359,lbs),uu____6361) ->
              let uu____6372 =
                let uu____6374 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6374  in
              if uu____6372
              then
                FStar_All.pipe_right lbs
                  (FStar_List.iter
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        check_term1
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp))
              else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l,univs,binders,comp,flags) ->
              let uu____6397 =
                let uu____6399 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6399  in
              if uu____6397
              then
                let arrow =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs arrow
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____6420 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____6421 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____6428 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____6429 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____6430 -> ()
          | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____6431 -> ()
          | FStar_Syntax_Syntax.Sig_fail uu____6442 ->
              failwith "Impossible (Already handled)"
          | FStar_Syntax_Syntax.Sig_splice uu____6456 ->
              failwith "Impossible (Already handled)"
           in
        let uu____6464 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____6464 then () else FStar_List.iter check_sigelt exports
  
let (extract_interface :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul)
  =
  fun en  ->
    fun m  ->
      let is_abstract = FStar_List.contains FStar_Syntax_Syntax.Abstract  in
      let is_irreducible =
        FStar_List.contains FStar_Syntax_Syntax.Irreducible  in
      let is_assume = FStar_List.contains FStar_Syntax_Syntax.Assumption  in
      let filter_out_abstract =
        FStar_List.filter
          (fun q  ->
             Prims.op_Negation
               (((q = FStar_Syntax_Syntax.Abstract) ||
                   (q = FStar_Syntax_Syntax.Irreducible))
                  || (q = FStar_Syntax_Syntax.Visible_default)))
         in
      let filter_out_abstract_and_noeq =
        FStar_List.filter
          (fun q  ->
             Prims.op_Negation
               (((((q = FStar_Syntax_Syntax.Abstract) ||
                     (q = FStar_Syntax_Syntax.Noeq))
                    || (q = FStar_Syntax_Syntax.Unopteq))
                   || (q = FStar_Syntax_Syntax.Irreducible))
                  || (q = FStar_Syntax_Syntax.Visible_default)))
         in
      let filter_out_abstract_and_inline =
        FStar_List.filter
          (fun q  ->
             Prims.op_Negation
               (((((q = FStar_Syntax_Syntax.Abstract) ||
                     (q = FStar_Syntax_Syntax.Irreducible))
                    || (q = FStar_Syntax_Syntax.Visible_default))
                   || (q = FStar_Syntax_Syntax.Inline_for_extraction))
                  ||
                  (q = FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
         in
      let abstract_inductive_tycons = FStar_Util.mk_ref []  in
      let abstract_inductive_datacons = FStar_Util.mk_ref []  in
      let is_projector_or_discriminator_of_an_abstract_inductive quals =
        FStar_List.existsML
          (fun q  ->
             match q with
             | FStar_Syntax_Syntax.Discriminator l -> true
             | FStar_Syntax_Syntax.Projector (l,uu____6570) -> true
             | uu____6572 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____6602 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____6641 ->
                   let uu____6642 =
                     let uu____6649 =
                       let uu____6650 =
                         let uu____6665 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____6665)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____6650  in
                     FStar_Syntax_Syntax.mk uu____6649  in
                   uu____6642 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____6682,uu____6683) ->
            let s1 =
              let uu___1188_6693 = s  in
              let uu____6694 =
                let uu____6695 =
                  let uu____6702 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____6702)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____6695  in
              let uu____6703 =
                let uu____6706 =
                  let uu____6709 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____6709  in
                FStar_Syntax_Syntax.Assumption :: uu____6706  in
              {
                FStar_Syntax_Syntax.sigel = uu____6694;
                FStar_Syntax_Syntax.sigrng =
                  (uu___1188_6693.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____6703;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___1188_6693.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___1188_6693.FStar_Syntax_Syntax.sigattrs);
                FStar_Syntax_Syntax.sigopts =
                  (uu___1188_6693.FStar_Syntax_Syntax.sigopts)
              }  in
            [s1]
        | uu____6712 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____6737 lbdef =
        match uu____6737 with
        | (uvs,t) ->
            let attrs =
              let uu____6748 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____6748
              then
                let uu____6753 =
                  let uu____6754 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____6754
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____6753 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___1201_6757 = s  in
            let uu____6758 =
              let uu____6761 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____6761  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___1201_6757.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____6758;
              FStar_Syntax_Syntax.sigmeta =
                (uu___1201_6757.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs;
              FStar_Syntax_Syntax.sigopts =
                (uu___1201_6757.FStar_Syntax_Syntax.sigopts)
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____6779 -> failwith "Impossible!"  in
        let c_opt =
          let uu____6786 = FStar_Syntax_Util.is_unit t  in
          if uu____6786
          then
            let uu____6793 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____6793
          else
            (let uu____6800 =
               let uu____6801 = FStar_Syntax_Subst.compress t  in
               uu____6801.FStar_Syntax_Syntax.n  in
             match uu____6800 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____6808,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____6832 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____6844 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____6844
            then false
            else
              (let uu____6851 = FStar_Syntax_Util.is_pure_or_ghost_comp c  in
               if uu____6851
               then true
               else
                 (let uu____6858 = comp_effect_name c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____6858))
         in
      let extract_sigelt s =
        (let uu____6870 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____6870
         then
           let uu____6873 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____6873
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____6880 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____6900 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____6919 ->
             failwith
               "Impossible! extract_interface: trying to extract splice"
         | FStar_Syntax_Syntax.Sig_fail uu____6929 ->
             failwith
               "Impossible! extract_interface: trying to extract Sig_fail"
         | FStar_Syntax_Syntax.Sig_bundle (sigelts,lidents) ->
             if is_abstract s.FStar_Syntax_Syntax.sigquals
             then
               FStar_All.pipe_right sigelts
                 (FStar_List.fold_left
                    (fun sigelts1  ->
                       fun s1  ->
                         match s1.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_inductive_typ
                             (lid,uu____6981,uu____6982,uu____6983,uu____6984,uu____6985)
                             ->
                             ((let uu____6995 =
                                 let uu____6998 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____6998  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____6995);
                              (let uu____7047 = vals_of_abstract_inductive s1
                                  in
                               FStar_List.append uu____7047 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____7051,uu____7052,uu____7053,uu____7054,uu____7055)
                             ->
                             ((let uu____7063 =
                                 let uu____7066 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____7066  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____7063);
                              sigelts1)
                         | uu____7115 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____7124 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____7124
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____7134 =
                    let uu___1267_7135 = s  in
                    let uu____7136 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1267_7135.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1267_7135.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____7136;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1267_7135.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1267_7135.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1267_7135.FStar_Syntax_Syntax.sigopts)
                    }  in
                  [uu____7134])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____7147 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____7147
             then []
             else
               (let uu____7154 = lbs  in
                match uu____7154 with
                | (flbs,slbs) ->
                    let typs_and_defs =
                      FStar_All.pipe_right slbs
                        (FStar_List.map
                           (fun lb  ->
                              ((lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp),
                                (lb.FStar_Syntax_Syntax.lbdef))))
                       in
                    let is_lemma =
                      FStar_List.existsML
                        (fun uu____7216  ->
                           match uu____7216 with
                           | (uu____7224,t,uu____7226) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____7243  ->
                             match uu____7243 with
                             | (u,t,d) -> val_of_lb s lid (u, t) d) lids
                        typs_and_defs
                       in
                    if
                      ((is_abstract s.FStar_Syntax_Syntax.sigquals) ||
                         (is_irreducible s.FStar_Syntax_Syntax.sigquals))
                        || is_lemma
                    then vals
                    else
                      (let should_keep_defs =
                         FStar_List.existsML
                           (fun uu____7270  ->
                              match uu____7270 with
                              | (uu____7278,t,uu____7280) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____7292,uu____7293) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____7301 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____7330 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____7330) uu____7301
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____7334 =
                    let uu___1309_7335 = s  in
                    let uu____7336 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1309_7335.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1309_7335.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____7336;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1309_7335.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1309_7335.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1309_7335.FStar_Syntax_Syntax.sigopts)
                    }  in
                  [uu____7334]
                else [])
             else
               (let uu____7343 =
                  let uu___1311_7344 = s  in
                  let uu____7345 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1311_7344.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1311_7344.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____7345;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1311_7344.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1311_7344.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___1311_7344.FStar_Syntax_Syntax.sigopts)
                  }  in
                [uu____7343])
         | FStar_Syntax_Syntax.Sig_new_effect uu____7348 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____7349 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7350 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____7363 -> [s]
         | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____7364 -> [s])
         in
      let uu___1323_7375 = m  in
      let uu____7376 =
        let uu____7377 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____7377 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___1323_7375.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____7376;
        FStar_Syntax_Syntax.exports =
          (uu___1323_7375.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface = true
      }
  
let (snapshot_context :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____7428  -> FStar_TypeChecker_Env.snapshot env msg)
  
let (rollback_context :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string ->
      (Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____7475  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____7490 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____7490
  
let (pop_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      rollback_context env.FStar_TypeChecker_Env.solver msg
        FStar_Pervasives_Native.None
  
let (tc_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
        FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun modul  ->
      let verify =
        let uu____7562 =
          FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
        FStar_Options.should_verify uu____7562  in
      let action = if verify then "Verifying" else "Lax-checking"  in
      let label =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation"  in
      (let uu____7581 = FStar_Options.debug_any ()  in
       if uu____7581
       then
         let uu____7584 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
         FStar_Util.print3 "%s %s of %s\n" action label uu____7584
       else ());
      (let name =
         let uu____7591 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") uu____7591
          in
       let env1 =
         let uu___1348_7601 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___1348_7601.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___1348_7601.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___1348_7601.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___1348_7601.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___1348_7601.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___1348_7601.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___1348_7601.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___1348_7601.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___1348_7601.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___1348_7601.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___1348_7601.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___1348_7601.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___1348_7601.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___1348_7601.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___1348_7601.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___1348_7601.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___1348_7601.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___1348_7601.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___1348_7601.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___1348_7601.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___1348_7601.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___1348_7601.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___1348_7601.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___1348_7601.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___1348_7601.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___1348_7601.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___1348_7601.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___1348_7601.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___1348_7601.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___1348_7601.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___1348_7601.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___1348_7601.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___1348_7601.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___1348_7601.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___1348_7601.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___1348_7601.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___1348_7601.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___1348_7601.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___1348_7601.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___1348_7601.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___1348_7601.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___1348_7601.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___1348_7601.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___1348_7601.FStar_TypeChecker_Env.erasable_types_tab)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____7603 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____7603 with
       | (ses,exports,env3) ->
           ((let uu___1356_7636 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___1356_7636.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___1356_7636.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___1356_7636.FStar_Syntax_Syntax.is_interface)
             }), exports, env3))
  
let (tc_more_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
          FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun modul  ->
      fun decls  ->
        let uu____7665 = tc_decls env decls  in
        match uu____7665 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___1365_7696 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___1365_7696.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___1365_7696.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___1365_7696.FStar_Syntax_Syntax.is_interface)
              }  in
            (modul1, exports, env1)
  
let rec (tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env0  ->
    fun m  ->
      fun iface_exists  ->
        let msg =
          let uu____7755 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____7755  in
        let env01 = push_context env0 msg  in
        let uu____7759 = tc_partial_modul env01 m  in
        match uu____7759 with
        | (modul,non_private_decls,env) ->
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
  fun loading_from_cache  ->
    fun iface_exists  ->
      fun en  ->
        fun m  ->
          fun exports  ->
            let should_extract_interface =
              ((((Prims.op_Negation loading_from_cache) &&
                   (Prims.op_Negation iface_exists))
                  && (FStar_Options.use_extracted_interfaces ()))
                 && (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
                &&
                (let uu____7796 = FStar_Errors.get_err_count ()  in
                 uu____7796 = Prims.int_zero)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____7807 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____7807
                then
                  let uu____7811 =
                    FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                  let uu____7813 =
                    let uu____7815 =
                      let uu____7817 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name
                         in
                      FStar_Options.should_verify uu____7817  in
                    if uu____7815 then "" else " (in lax mode) "  in
                  let uu____7825 =
                    let uu____7827 =
                      let uu____7829 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name
                         in
                      FStar_Options.dump_module uu____7829  in
                    if uu____7827
                    then
                      let uu____7833 =
                        let uu____7835 = FStar_Syntax_Print.modul_to_string m
                           in
                        Prims.op_Hat uu____7835 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____7833
                    else ""  in
                  let uu____7842 =
                    let uu____7844 =
                      let uu____7846 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name
                         in
                      FStar_Options.dump_module uu____7846  in
                    if uu____7844
                    then
                      let uu____7850 =
                        let uu____7852 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____7852 "\n"  in
                      Prims.op_Hat "\nto: " uu____7850
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    uu____7811 uu____7813 uu____7825 uu____7842
                else ());
               (let en0 =
                  let en0 =
                    let uu____7864 =
                      let uu____7866 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name
                         in
                      Prims.op_Hat "Ending modul " uu____7866  in
                    pop_context en uu____7864  in
                  let en01 =
                    let uu___1391_7870 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1391_7870.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1391_7870.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1391_7870.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1391_7870.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1391_7870.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1391_7870.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1391_7870.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1391_7870.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1391_7870.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1391_7870.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1391_7870.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1391_7870.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1391_7870.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1391_7870.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1391_7870.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1391_7870.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1391_7870.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.use_eq_strict =
                        (uu___1391_7870.FStar_TypeChecker_Env.use_eq_strict);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1391_7870.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1391_7870.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1391_7870.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1391_7870.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1391_7870.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1391_7870.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1391_7870.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1391_7870.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1391_7870.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1391_7870.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1391_7870.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1391_7870.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1391_7870.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1391_7870.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1391_7870.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1391_7870.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1391_7870.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1391_7870.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1391_7870.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1391_7870.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.mpreprocess =
                        (uu___1391_7870.FStar_TypeChecker_Env.mpreprocess);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1391_7870.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1391_7870.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1391_7870.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1391_7870.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1391_7870.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___1391_7870.FStar_TypeChecker_Env.erasable_types_tab)
                    }  in
                  let en02 =
                    let uu___1394_7872 = en01  in
                    let uu____7873 =
                      let uu____7888 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____7888, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1394_7872.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1394_7872.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1394_7872.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1394_7872.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1394_7872.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1394_7872.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1394_7872.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1394_7872.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1394_7872.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1394_7872.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1394_7872.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1394_7872.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1394_7872.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1394_7872.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1394_7872.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1394_7872.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1394_7872.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.use_eq_strict =
                        (uu___1394_7872.FStar_TypeChecker_Env.use_eq_strict);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1394_7872.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1394_7872.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1394_7872.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1394_7872.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1394_7872.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1394_7872.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1394_7872.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1394_7872.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1394_7872.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1394_7872.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1394_7872.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1394_7872.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1394_7872.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____7873;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1394_7872.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1394_7872.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1394_7872.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1394_7872.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1394_7872.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1394_7872.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.mpreprocess =
                        (uu___1394_7872.FStar_TypeChecker_Env.mpreprocess);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1394_7872.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1394_7872.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1394_7872.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1394_7872.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1394_7872.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1394_7872.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___1394_7872.FStar_TypeChecker_Env.erasable_types_tab)
                    }  in
                  let uu____7934 =
                    let uu____7936 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____7936  in
                  if uu____7934
                  then
                    ((let uu____7940 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____7940 (fun uu____7942  -> ()));
                     en02)
                  else en02  in
                let uu____7945 = tc_modul en0 modul_iface true  in
                match uu____7945 with
                | (modul_iface1,env) ->
                    ((let uu___1403_7958 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___1403_7958.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___1403_7958.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___1403_7958.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___1405_7962 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___1405_7962.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___1405_7962.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___1405_7962.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____7965 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____7965 FStar_Util.smap_clear);
               (let uu____8001 =
                  ((let uu____8005 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____8005) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____8008 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____8008)
                   in
                if uu____8001 then check_exports env modul exports else ());
               (let uu____8014 =
                  let uu____8015 =
                    let uu____8017 =
                      FStar_Ident.string_of_lid
                        modul.FStar_Syntax_Syntax.name
                       in
                    Prims.op_Hat "Ending modul " uu____8017  in
                  pop_context env uu____8015  in
                FStar_All.pipe_right uu____8014 (fun uu____8020  -> ()));
               (modul, env))

let (load_checked_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_TypeChecker_Env.env)
  =
  fun en  ->
    fun m  ->
      let env =
        FStar_TypeChecker_Env.set_current_module en
          m.FStar_Syntax_Syntax.name
         in
      let env1 =
        let uu____8034 =
          let uu____8036 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____8036  in
        push_context env uu____8034  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = add_sigelt_to_env env2 se true  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____8058 =
                         FStar_TypeChecker_Env.lookup_sigelt env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____8061 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____8061 with | (uu____8068,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____8093 = FStar_Options.debug_any ()  in
         if uu____8093
         then
           let uu____8096 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____8096
         else ());
        (let uu____8108 =
           let uu____8110 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Options.dump_module uu____8110  in
         if uu____8108
         then
           let uu____8113 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____8113
         else ());
        (let env1 =
           let uu___1435_8119 = env  in
           let uu____8120 =
             let uu____8122 =
               let uu____8124 =
                 FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
               FStar_Options.should_verify uu____8124  in
             Prims.op_Negation uu____8122  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___1435_8119.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___1435_8119.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___1435_8119.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___1435_8119.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___1435_8119.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___1435_8119.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___1435_8119.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___1435_8119.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___1435_8119.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___1435_8119.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___1435_8119.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___1435_8119.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___1435_8119.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___1435_8119.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___1435_8119.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___1435_8119.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___1435_8119.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.use_eq_strict =
               (uu___1435_8119.FStar_TypeChecker_Env.use_eq_strict);
             FStar_TypeChecker_Env.is_iface =
               (uu___1435_8119.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___1435_8119.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____8120;
             FStar_TypeChecker_Env.lax_universes =
               (uu___1435_8119.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___1435_8119.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___1435_8119.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___1435_8119.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___1435_8119.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___1435_8119.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___1435_8119.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___1435_8119.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___1435_8119.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___1435_8119.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___1435_8119.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___1435_8119.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___1435_8119.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___1435_8119.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___1435_8119.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___1435_8119.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___1435_8119.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (uu___1435_8119.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (uu___1435_8119.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.identifier_info =
               (uu___1435_8119.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___1435_8119.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___1435_8119.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___1435_8119.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___1435_8119.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___1435_8119.FStar_TypeChecker_Env.erasable_types_tab)
           }  in
         let uu____8126 = tc_modul env1 m b  in
         match uu____8126 with
         | (m1,env2) ->
             ((let uu____8138 =
                 let uu____8140 =
                   FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name  in
                 FStar_Options.dump_module uu____8140  in
               if uu____8138
               then
                 let uu____8143 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____8143
               else ());
              (let uu____8149 =
                 (let uu____8153 =
                    FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name  in
                  FStar_Options.dump_module uu____8153) &&
                   (let uu____8156 =
                      FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name
                       in
                    FStar_Options.debug_at_level uu____8156
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____8149
               then
                 let normalize_toplevel_lets se =
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_let ((b1,lbs),ids) ->
                       let n =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Reify;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.AllowUnboundUniverses]
                          in
                       let update lb =
                         let uu____8194 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____8194 with
                         | (univnames,e) ->
                             let uu___1457_8201 = lb  in
                             let uu____8202 =
                               let uu____8205 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames
                                  in
                               n uu____8205 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1457_8201.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1457_8201.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1457_8201.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1457_8201.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____8202;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1457_8201.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1457_8201.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___1459_8206 = se  in
                       let uu____8207 =
                         let uu____8208 =
                           let uu____8215 =
                             let uu____8216 = FStar_List.map update lbs  in
                             (b1, uu____8216)  in
                           (uu____8215, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____8208  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____8207;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1459_8206.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1459_8206.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1459_8206.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___1459_8206.FStar_Syntax_Syntax.sigattrs);
                         FStar_Syntax_Syntax.sigopts =
                           (uu___1459_8206.FStar_Syntax_Syntax.sigopts)
                       }
                   | uu____8224 -> se  in
                 let normalized_module =
                   let uu___1463_8226 = m1  in
                   let uu____8227 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___1463_8226.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____8227;
                     FStar_Syntax_Syntax.exports =
                       (uu___1463_8226.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___1463_8226.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____8228 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____8228
               else ());
              (m1, env2)))
  