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
                 let env1 = FStar_TypeChecker_Env.set_range env r  in
                 let uu____2015 =
                   FStar_TypeChecker_TcEffect.dmff_cps_and_elaborate env1 ne
                    in
                 (match uu____2015 with
                  | (ses,ne1,lift_from_pure_opt) ->
                      let effect_and_lift_ses =
                        match lift_from_pure_opt with
                        | FStar_Pervasives_Native.Some lift ->
                            [(let uu___346_2054 = se1  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___346_2054.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___346_2054.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___346_2054.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___346_2054.FStar_Syntax_Syntax.sigattrs);
                                FStar_Syntax_Syntax.sigopts =
                                  (uu___346_2054.FStar_Syntax_Syntax.sigopts)
                              });
                            lift]
                        | FStar_Pervasives_Native.None  ->
                            [(let uu___349_2056 = se1  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___349_2056.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___349_2056.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___349_2056.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___349_2056.FStar_Syntax_Syntax.sigattrs);
                                FStar_Syntax_Syntax.sigopts =
                                  (uu___349_2056.FStar_Syntax_Syntax.sigopts)
                              })]
                         in
                      ([], (FStar_List.append ses effect_and_lift_ses), env0))
               else
                 (let ne1 =
                    let uu____2064 =
                      (FStar_Options.use_two_phase_tc ()) &&
                        (FStar_TypeChecker_Env.should_verify env)
                       in
                    if uu____2064
                    then
                      let ne1 =
                        let uu____2068 =
                          let uu____2069 =
                            let uu____2070 =
                              FStar_TypeChecker_TcEffect.tc_eff_decl
                                (let uu___353_2073 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___353_2073.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___353_2073.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___353_2073.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___353_2073.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___353_2073.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___353_2073.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___353_2073.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___353_2073.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___353_2073.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___353_2073.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___353_2073.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___353_2073.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___353_2073.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___353_2073.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___353_2073.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___353_2073.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___353_2073.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___353_2073.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___353_2073.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___353_2073.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___353_2073.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 = true;
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___353_2073.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___353_2073.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___353_2073.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___353_2073.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___353_2073.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___353_2073.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___353_2073.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___353_2073.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___353_2073.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___353_2073.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___353_2073.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___353_2073.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___353_2073.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___353_2073.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___353_2073.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___353_2073.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___353_2073.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___353_2073.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___353_2073.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___353_2073.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___353_2073.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___353_2073.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___353_2073.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) ne se1.FStar_Syntax_Syntax.sigquals
                               in
                            FStar_All.pipe_right uu____2070
                              (fun ne1  ->
                                 let uu___356_2079 = se1  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___356_2079.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals =
                                     (uu___356_2079.FStar_Syntax_Syntax.sigquals);
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___356_2079.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___356_2079.FStar_Syntax_Syntax.sigattrs);
                                   FStar_Syntax_Syntax.sigopts =
                                     (uu___356_2079.FStar_Syntax_Syntax.sigopts)
                                 })
                             in
                          FStar_All.pipe_right uu____2069
                            (FStar_TypeChecker_Normalize.elim_uvars env)
                           in
                        FStar_All.pipe_right uu____2068
                          FStar_Syntax_Util.eff_decl_of_new_effect
                         in
                      ((let uu____2081 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "TwoPhases")
                           in
                        if uu____2081
                        then
                          let uu____2086 =
                            FStar_Syntax_Print.sigelt_to_string
                              (let uu___360_2090 = se1  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___360_2090.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals =
                                   (uu___360_2090.FStar_Syntax_Syntax.sigquals);
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___360_2090.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___360_2090.FStar_Syntax_Syntax.sigattrs);
                                 FStar_Syntax_Syntax.sigopts =
                                   (uu___360_2090.FStar_Syntax_Syntax.sigopts)
                               })
                             in
                          FStar_Util.print1 "Effect decl after phase 1: %s\n"
                            uu____2086
                        else ());
                       ne1)
                    else ne  in
                  let ne2 =
                    FStar_TypeChecker_TcEffect.tc_eff_decl env ne1
                      se1.FStar_Syntax_Syntax.sigquals
                     in
                  let se2 =
                    let uu___365_2098 = se1  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_new_effect ne2);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___365_2098.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___365_2098.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___365_2098.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___365_2098.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___365_2098.FStar_Syntax_Syntax.sigopts)
                    }  in
                  ([se2], [], env0))
           | FStar_Syntax_Syntax.Sig_sub_effect sub ->
               let sub1 = FStar_TypeChecker_TcEffect.tc_lift env sub r  in
               let se2 =
                 let uu___371_2106 = se1  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_sub_effect sub1);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___371_2106.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___371_2106.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___371_2106.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___371_2106.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (uu___371_2106.FStar_Syntax_Syntax.sigopts)
                 }  in
               ([se2], [], env)
           | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
               let uu____2120 =
                 let uu____2129 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env)
                    in
                 if uu____2129
                 then
                   let uu____2140 =
                     let uu____2141 =
                       let uu____2142 =
                         FStar_TypeChecker_TcEffect.tc_effect_abbrev
                           (let uu___382_2153 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___382_2153.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___382_2153.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___382_2153.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___382_2153.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___382_2153.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___382_2153.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___382_2153.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___382_2153.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___382_2153.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___382_2153.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___382_2153.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___382_2153.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___382_2153.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___382_2153.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___382_2153.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___382_2153.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___382_2153.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___382_2153.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___382_2153.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___382_2153.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___382_2153.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 = true;
                              FStar_TypeChecker_Env.failhard =
                                (uu___382_2153.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___382_2153.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___382_2153.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___382_2153.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___382_2153.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___382_2153.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___382_2153.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___382_2153.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___382_2153.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___382_2153.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___382_2153.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___382_2153.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___382_2153.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___382_2153.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___382_2153.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___382_2153.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___382_2153.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___382_2153.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___382_2153.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___382_2153.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___382_2153.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___382_2153.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___382_2153.FStar_TypeChecker_Env.erasable_types_tab)
                            }) (lid, uvs, tps, c) r
                          in
                       FStar_All.pipe_right uu____2142
                         (fun uu____2170  ->
                            match uu____2170 with
                            | (lid1,uvs1,tps1,c1) ->
                                let uu___389_2183 = se1  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_effect_abbrev
                                       (lid1, uvs1, tps1, c1, flags));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___389_2183.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___389_2183.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___389_2183.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___389_2183.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___389_2183.FStar_Syntax_Syntax.sigopts)
                                })
                        in
                     FStar_All.pipe_right uu____2141
                       (FStar_TypeChecker_Normalize.elim_uvars env)
                      in
                   FStar_All.pipe_right uu____2140
                     (fun se2  ->
                        match se2.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_effect_abbrev
                            (lid1,uvs1,tps1,c1,uu____2213) ->
                            (lid1, uvs1, tps1, c1)
                        | uu____2218 ->
                            failwith
                              "Did not expect Sig_effect_abbrev to not be one after phase 1")
                 else (lid, uvs, tps, c)  in
               (match uu____2120 with
                | (lid1,uvs1,tps1,c1) ->
                    let uu____2244 =
                      FStar_TypeChecker_TcEffect.tc_effect_abbrev env
                        (lid1, uvs1, tps1, c1) r
                       in
                    (match uu____2244 with
                     | (lid2,uvs2,tps2,c2) ->
                         let se2 =
                           let uu___410_2268 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  (lid2, uvs2, tps2, c2, flags));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___410_2268.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___410_2268.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___410_2268.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___410_2268.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___410_2268.FStar_Syntax_Syntax.sigopts)
                           }  in
                         ([se2], [], env0)))
           | FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2275,uu____2276,uu____2277) when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___0_2282  ->
                       match uu___0_2282 with
                       | FStar_Syntax_Syntax.OnlyName  -> true
                       | uu____2285 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_let (uu____2291,uu____2292) when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___0_2301  ->
                       match uu___0_2301 with
                       | FStar_Syntax_Syntax.OnlyName  -> true
                       | uu____2304 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
               let env1 = FStar_TypeChecker_Env.set_range env r  in
               ((let uu____2315 = FStar_TypeChecker_Env.lid_exists env1 lid
                    in
                 if uu____2315
                 then
                   let uu____2318 =
                     let uu____2324 =
                       let uu____2326 = FStar_Ident.string_of_lid lid  in
                       FStar_Util.format1
                         "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                         uu____2326
                        in
                     (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                       uu____2324)
                      in
                   FStar_Errors.raise_error uu____2318 r
                 else ());
                (let uu____2332 =
                   let uu____2341 =
                     (FStar_Options.use_two_phase_tc ()) &&
                       (FStar_TypeChecker_Env.should_verify env1)
                      in
                   if uu____2341
                   then
                     let uu____2352 =
                       tc_declare_typ
                         (let uu___434_2355 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___434_2355.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___434_2355.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___434_2355.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___434_2355.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___434_2355.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___434_2355.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___434_2355.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___434_2355.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___434_2355.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___434_2355.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___434_2355.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___434_2355.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___434_2355.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___434_2355.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___434_2355.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___434_2355.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___434_2355.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___434_2355.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___434_2355.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___434_2355.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___434_2355.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___434_2355.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___434_2355.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___434_2355.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___434_2355.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___434_2355.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___434_2355.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___434_2355.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___434_2355.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___434_2355.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___434_2355.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___434_2355.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___434_2355.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___434_2355.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___434_2355.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___434_2355.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___434_2355.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___434_2355.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___434_2355.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___434_2355.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___434_2355.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___434_2355.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___434_2355.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___434_2355.FStar_TypeChecker_Env.erasable_types_tab)
                          }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng
                        in
                     match uu____2352 with
                     | (uvs1,t1) ->
                         ((let uu____2381 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "TwoPhases")
                              in
                           if uu____2381
                           then
                             let uu____2386 =
                               FStar_Syntax_Print.term_to_string t1  in
                             let uu____2388 =
                               FStar_Syntax_Print.univ_names_to_string uvs1
                                in
                             FStar_Util.print2
                               "Val declaration after phase 1: %s and uvs: %s\n"
                               uu____2386 uu____2388
                           else ());
                          (uvs1, t1))
                   else (uvs, t)  in
                 match uu____2332 with
                 | (uvs1,t1) ->
                     let uu____2423 =
                       tc_declare_typ env1 (uvs1, t1)
                         se1.FStar_Syntax_Syntax.sigrng
                        in
                     (match uu____2423 with
                      | (uvs2,t2) ->
                          ([(let uu___447_2453 = se1  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (lid, uvs2, t2));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___447_2453.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___447_2453.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___447_2453.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___447_2453.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___447_2453.FStar_Syntax_Syntax.sigopts)
                             })], [], env0))))
           | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
               let env1 = FStar_TypeChecker_Env.set_range env r  in
               let uu____2458 =
                 let uu____2467 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env1)
                    in
                 if uu____2467
                 then
                   let uu____2478 =
                     tc_assume
                       (let uu___456_2481 = env1  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___456_2481.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___456_2481.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___456_2481.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___456_2481.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___456_2481.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___456_2481.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___456_2481.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___456_2481.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___456_2481.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___456_2481.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___456_2481.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___456_2481.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___456_2481.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___456_2481.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level =
                            (uu___456_2481.FStar_TypeChecker_Env.top_level);
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___456_2481.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___456_2481.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.use_eq_strict =
                            (uu___456_2481.FStar_TypeChecker_Env.use_eq_strict);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___456_2481.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___456_2481.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax = true;
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___456_2481.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 = true;
                          FStar_TypeChecker_Env.failhard =
                            (uu___456_2481.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___456_2481.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___456_2481.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___456_2481.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___456_2481.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___456_2481.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___456_2481.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___456_2481.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___456_2481.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___456_2481.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___456_2481.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___456_2481.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___456_2481.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.try_solve_implicits_hook =
                            (uu___456_2481.FStar_TypeChecker_Env.try_solve_implicits_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___456_2481.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.mpreprocess =
                            (uu___456_2481.FStar_TypeChecker_Env.mpreprocess);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___456_2481.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___456_2481.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___456_2481.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___456_2481.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___456_2481.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___456_2481.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (uu___456_2481.FStar_TypeChecker_Env.erasable_types_tab)
                        }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng
                      in
                   match uu____2478 with
                   | (uvs1,t1) ->
                       ((let uu____2507 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "TwoPhases")
                            in
                         if uu____2507
                         then
                           let uu____2512 =
                             FStar_Syntax_Print.term_to_string t1  in
                           let uu____2514 =
                             FStar_Syntax_Print.univ_names_to_string uvs1  in
                           FStar_Util.print2
                             "Assume after phase 1: %s and uvs: %s\n"
                             uu____2512 uu____2514
                         else ());
                        (uvs1, t1))
                 else (uvs, t)  in
               (match uu____2458 with
                | (uvs1,t1) ->
                    let uu____2549 =
                      tc_assume env1 (uvs1, t1)
                        se1.FStar_Syntax_Syntax.sigrng
                       in
                    (match uu____2549 with
                     | (uvs2,t2) ->
                         ([(let uu___469_2579 = se1  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_assume
                                   (lid, uvs2, t2));
                              FStar_Syntax_Syntax.sigrng =
                                (uu___469_2579.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___469_2579.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___469_2579.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___469_2579.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (uu___469_2579.FStar_Syntax_Syntax.sigopts)
                            })], [], env0)))
           | FStar_Syntax_Syntax.Sig_main e ->
               let env1 = FStar_TypeChecker_Env.set_range env r  in
               let env2 =
                 FStar_TypeChecker_Env.set_expected_typ env1
                   FStar_Syntax_Syntax.t_unit
                  in
               let uu____2583 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
               (match uu____2583 with
                | (e1,c,g1) ->
                    let uu____2603 =
                      let uu____2610 = FStar_TypeChecker_Common.lcomp_comp c
                         in
                      match uu____2610 with
                      | (c1,g_lc) ->
                          let uu____2623 =
                            let uu____2630 =
                              let uu____2633 =
                                FStar_Syntax_Util.ml_comp
                                  FStar_Syntax_Syntax.t_unit r
                                 in
                              FStar_Pervasives_Native.Some uu____2633  in
                            FStar_TypeChecker_TcTerm.check_expected_effect
                              env2 uu____2630 (e1, c1)
                             in
                          (match uu____2623 with
                           | (e2,_x,g) ->
                               let uu____2643 =
                                 FStar_TypeChecker_Env.conj_guard g_lc g  in
                               (e2, _x, uu____2643))
                       in
                    (match uu____2603 with
                     | (e2,uu____2655,g) ->
                         ((let uu____2658 =
                             FStar_TypeChecker_Env.conj_guard g1 g  in
                           FStar_TypeChecker_Rel.force_trivial_guard env2
                             uu____2658);
                          (let se2 =
                             let uu___491_2660 = se1  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_main e2);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___491_2660.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___491_2660.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___491_2660.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___491_2660.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___491_2660.FStar_Syntax_Syntax.sigopts)
                             }  in
                           ([se2], [], env0)))))
           | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
               ((let uu____2672 = FStar_Options.debug_any ()  in
                 if uu____2672
                 then
                   let uu____2675 =
                     FStar_Ident.string_of_lid
                       env.FStar_TypeChecker_Env.curmodule
                      in
                   let uu____2677 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print2 "%s: Found splice of (%s)\n" uu____2675
                     uu____2677
                 else ());
                (let uu____2682 =
                   FStar_TypeChecker_TcTerm.tc_tactic
                     FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_decls
                     env t
                    in
                 match uu____2682 with
                 | (t1,uu____2700,g) ->
                     (FStar_TypeChecker_Rel.force_trivial_guard env g;
                      (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                       let lids' =
                         FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                           ses
                          in
                       FStar_List.iter
                         (fun lid  ->
                            let uu____2714 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids'
                               in
                            match uu____2714 with
                            | FStar_Pervasives_Native.None  when
                                Prims.op_Negation
                                  env.FStar_TypeChecker_Env.nosynth
                                ->
                                let uu____2717 =
                                  let uu____2723 =
                                    let uu____2725 =
                                      FStar_Ident.string_of_lid lid  in
                                    let uu____2727 =
                                      let uu____2729 =
                                        FStar_List.map
                                          FStar_Ident.string_of_lid lids'
                                         in
                                      FStar_All.pipe_left
                                        (FStar_String.concat ", ") uu____2729
                                       in
                                    FStar_Util.format2
                                      "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                      uu____2725 uu____2727
                                     in
                                  (FStar_Errors.Fatal_SplicedUndef,
                                    uu____2723)
                                   in
                                FStar_Errors.raise_error uu____2717 r
                            | uu____2741 -> ()) lids;
                       (let dsenv =
                          FStar_List.fold_left
                            FStar_Syntax_DsEnv.push_sigelt_force
                            env.FStar_TypeChecker_Env.dsenv ses
                           in
                        let env1 =
                          let uu___512_2746 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___512_2746.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___512_2746.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___512_2746.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___512_2746.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___512_2746.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___512_2746.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___512_2746.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___512_2746.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___512_2746.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___512_2746.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___512_2746.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___512_2746.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___512_2746.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___512_2746.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___512_2746.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___512_2746.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___512_2746.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___512_2746.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___512_2746.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___512_2746.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___512_2746.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___512_2746.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___512_2746.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___512_2746.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___512_2746.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___512_2746.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___512_2746.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___512_2746.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___512_2746.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___512_2746.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___512_2746.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___512_2746.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___512_2746.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___512_2746.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___512_2746.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___512_2746.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___512_2746.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___512_2746.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___512_2746.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___512_2746.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___512_2746.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___512_2746.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv = dsenv;
                            FStar_TypeChecker_Env.nbe =
                              (uu___512_2746.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___512_2746.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___512_2746.FStar_TypeChecker_Env.erasable_types_tab)
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
                     let uu____2814 =
                       let uu____2816 =
                         let uu____2825 = drop_logic val_q  in
                         let uu____2828 = drop_logic q'  in
                         (uu____2825, uu____2828)  in
                       match uu____2816 with
                       | (val_q1,q'1) ->
                           ((FStar_List.length val_q1) =
                              (FStar_List.length q'1))
                             &&
                             (FStar_List.forall2
                                FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                        in
                     if uu____2814
                     then FStar_Pervasives_Native.Some q'
                     else
                       (let uu____2855 =
                          let uu____2861 =
                            let uu____2863 =
                              FStar_Syntax_Print.lid_to_string l  in
                            let uu____2865 =
                              FStar_Syntax_Print.quals_to_string val_q  in
                            let uu____2867 =
                              FStar_Syntax_Print.quals_to_string q'  in
                            FStar_Util.format3
                              "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                              uu____2863 uu____2865 uu____2867
                             in
                          (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                            uu____2861)
                           in
                        FStar_Errors.raise_error uu____2855 r)
                  in
               let rename_parameters lb =
                 let rename_in_typ def typ =
                   let typ1 = FStar_Syntax_Subst.compress typ  in
                   let def_bs =
                     let uu____2904 =
                       let uu____2905 = FStar_Syntax_Subst.compress def  in
                       uu____2905.FStar_Syntax_Syntax.n  in
                     match uu____2904 with
                     | FStar_Syntax_Syntax.Tm_abs
                         (binders,uu____2917,uu____2918) -> binders
                     | uu____2943 -> []  in
                   match typ1 with
                   | {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                         (val_bs,c);
                       FStar_Syntax_Syntax.pos = r1;
                       FStar_Syntax_Syntax.vars = uu____2955;_} ->
                       let has_auto_name bv =
                         let uu____2985 =
                           FStar_Ident.text_of_id
                             bv.FStar_Syntax_Syntax.ppname
                            in
                         FStar_Util.starts_with uu____2985
                           FStar_Ident.reserved_prefix
                          in
                       let rec rename_binders def_bs1 val_bs1 =
                         match (def_bs1, val_bs1) with
                         | ([],uu____3062) -> val_bs1
                         | (uu____3093,[]) -> val_bs1
                         | ((body_bv,uu____3125)::bt,(val_bv,aqual)::vt) ->
                             let uu____3182 =
                               let uu____3189 =
                                 let uu____3196 = has_auto_name body_bv  in
                                 let uu____3198 = has_auto_name val_bv  in
                                 (uu____3196, uu____3198)  in
                               match uu____3189 with
                               | (true ,uu____3208) -> (val_bv, aqual)
                               | (false ,true ) ->
                                   let uu____3219 =
                                     let uu___581_3220 = val_bv  in
                                     let uu____3221 =
                                       let uu____3222 =
                                         let uu____3228 =
                                           FStar_Ident.text_of_id
                                             body_bv.FStar_Syntax_Syntax.ppname
                                            in
                                         let uu____3230 =
                                           FStar_Ident.range_of_id
                                             val_bv.FStar_Syntax_Syntax.ppname
                                            in
                                         (uu____3228, uu____3230)  in
                                       FStar_Ident.mk_ident uu____3222  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         uu____3221;
                                       FStar_Syntax_Syntax.index =
                                         (uu___581_3220.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (uu___581_3220.FStar_Syntax_Syntax.sort)
                                     }  in
                                   (uu____3219, aqual)
                               | (false ,false ) -> (val_bv, aqual)  in
                             let uu____3240 = rename_binders bt vt  in
                             uu____3182 :: uu____3240
                          in
                       let uu____3255 =
                         let uu____3262 =
                           let uu____3263 =
                             let uu____3278 = rename_binders def_bs val_bs
                                in
                             (uu____3278, c)  in
                           FStar_Syntax_Syntax.Tm_arrow uu____3263  in
                         FStar_Syntax_Syntax.mk uu____3262  in
                       uu____3255 FStar_Pervasives_Native.None r1
                   | uu____3297 -> typ1  in
                 let uu___587_3298 = lb  in
                 let uu____3299 =
                   rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                     lb.FStar_Syntax_Syntax.lbtyp
                    in
                 {
                   FStar_Syntax_Syntax.lbname =
                     (uu___587_3298.FStar_Syntax_Syntax.lbname);
                   FStar_Syntax_Syntax.lbunivs =
                     (uu___587_3298.FStar_Syntax_Syntax.lbunivs);
                   FStar_Syntax_Syntax.lbtyp = uu____3299;
                   FStar_Syntax_Syntax.lbeff =
                     (uu___587_3298.FStar_Syntax_Syntax.lbeff);
                   FStar_Syntax_Syntax.lbdef =
                     (uu___587_3298.FStar_Syntax_Syntax.lbdef);
                   FStar_Syntax_Syntax.lbattrs =
                     (uu___587_3298.FStar_Syntax_Syntax.lbattrs);
                   FStar_Syntax_Syntax.lbpos =
                     (uu___587_3298.FStar_Syntax_Syntax.lbpos)
                 }  in
               let uu____3302 =
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.fold_left
                      (fun uu____3357  ->
                         fun lb  ->
                           match uu____3357 with
                           | (gen,lbs1,quals_opt) ->
                               let lbname =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu____3403 =
                                 let uu____3415 =
                                   FStar_TypeChecker_Env.try_lookup_val_decl
                                     env1
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 match uu____3415 with
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
                                       | uu____3495 ->
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
                                      (let uu____3542 =
                                         FStar_Syntax_Syntax.mk_lb
                                           ((FStar_Util.Inr lbname), uvs,
                                             FStar_Parser_Const.effect_ALL_lid,
                                             tval, def, [],
                                             (lb.FStar_Syntax_Syntax.lbpos))
                                          in
                                       (false, uu____3542, quals_opt1)))
                                  in
                               (match uu____3403 with
                                | (gen1,lb1,quals_opt1) ->
                                    (gen1, (lb1 :: lbs1), quals_opt1)))
                      (true, [],
                        (if se1.FStar_Syntax_Syntax.sigquals = []
                         then FStar_Pervasives_Native.None
                         else
                           FStar_Pervasives_Native.Some
                             (se1.FStar_Syntax_Syntax.sigquals))))
                  in
               (match uu____3302 with
                | (should_generalize,lbs',quals_opt) ->
                    let quals =
                      match quals_opt with
                      | FStar_Pervasives_Native.None  ->
                          [FStar_Syntax_Syntax.Visible_default]
                      | FStar_Pervasives_Native.Some q ->
                          let uu____3646 =
                            FStar_All.pipe_right q
                              (FStar_Util.for_some
                                 (fun uu___1_3652  ->
                                    match uu___1_3652 with
                                    | FStar_Syntax_Syntax.Irreducible  ->
                                        true
                                    | FStar_Syntax_Syntax.Visible_default  ->
                                        true
                                    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                         -> true
                                    | uu____3657 -> false))
                             in
                          if uu____3646
                          then q
                          else FStar_Syntax_Syntax.Visible_default :: q
                       in
                    let lbs'1 = FStar_List.rev lbs'  in
                    let uu____3667 =
                      let uu____3676 =
                        FStar_Syntax_Util.extract_attr'
                          FStar_Parser_Const.preprocess_with
                          se1.FStar_Syntax_Syntax.sigattrs
                         in
                      match uu____3676 with
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
                    (match uu____3667 with
                     | (attrs,pre_tau) ->
                         let se2 =
                           let uu___645_3781 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___645_3781.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___645_3781.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___645_3781.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___645_3781.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs = attrs;
                             FStar_Syntax_Syntax.sigopts =
                               (uu___645_3781.FStar_Syntax_Syntax.sigopts)
                           }  in
                         let preprocess_lb tau lb =
                           let lbdef =
                             FStar_TypeChecker_Env.preprocess env1 tau
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           (let uu____3795 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TwoPhases")
                               in
                            if uu____3795
                            then
                              let uu____3800 =
                                FStar_Syntax_Print.term_to_string lbdef  in
                              FStar_Util.print1 "lb preprocessed into: %s\n"
                                uu____3800
                            else ());
                           (let uu___654_3805 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___654_3805.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___654_3805.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___654_3805.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___654_3805.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___654_3805.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___654_3805.FStar_Syntax_Syntax.lbpos)
                            })
                            in
                         let lbs'2 =
                           match pre_tau with
                           | FStar_Pervasives_Native.Some tau ->
                               FStar_List.map (preprocess_lb tau) lbs'1
                           | FStar_Pervasives_Native.None  -> lbs'1  in
                         let e =
                           let uu____3815 =
                             let uu____3822 =
                               let uu____3823 =
                                 let uu____3837 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_constant
                                        FStar_Const.Const_unit)
                                     FStar_Pervasives_Native.None r
                                    in
                                 (((FStar_Pervasives_Native.fst lbs), lbs'2),
                                   uu____3837)
                                  in
                               FStar_Syntax_Syntax.Tm_let uu____3823  in
                             FStar_Syntax_Syntax.mk uu____3822  in
                           uu____3815 FStar_Pervasives_Native.None r  in
                         let env' =
                           let uu___661_3856 = env1  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___661_3856.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___661_3856.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___661_3856.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___661_3856.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___661_3856.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___661_3856.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___661_3856.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___661_3856.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___661_3856.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___661_3856.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___661_3856.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___661_3856.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               should_generalize;
                             FStar_TypeChecker_Env.letrecs =
                               (uu___661_3856.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = true;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___661_3856.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___661_3856.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___661_3856.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___661_3856.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___661_3856.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___661_3856.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___661_3856.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___661_3856.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___661_3856.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___661_3856.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___661_3856.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___661_3856.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___661_3856.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___661_3856.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___661_3856.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___661_3856.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___661_3856.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___661_3856.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___661_3856.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___661_3856.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___661_3856.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___661_3856.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___661_3856.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___661_3856.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___661_3856.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___661_3856.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___661_3856.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___661_3856.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___661_3856.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___661_3856.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___661_3856.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let e1 =
                           let uu____3859 =
                             (FStar_Options.use_two_phase_tc ()) &&
                               (FStar_TypeChecker_Env.should_verify env')
                              in
                           if uu____3859
                           then
                             let drop_lbtyp e_lax =
                               let uu____3868 =
                                 let uu____3869 =
                                   FStar_Syntax_Subst.compress e_lax  in
                                 uu____3869.FStar_Syntax_Syntax.n  in
                               match uu____3868 with
                               | FStar_Syntax_Syntax.Tm_let
                                   ((false ,lb::[]),e2) ->
                                   let lb_unannotated =
                                     let uu____3891 =
                                       let uu____3892 =
                                         FStar_Syntax_Subst.compress e  in
                                       uu____3892.FStar_Syntax_Syntax.n  in
                                     match uu____3891 with
                                     | FStar_Syntax_Syntax.Tm_let
                                         ((uu____3896,lb1::[]),uu____3898) ->
                                         let uu____3914 =
                                           let uu____3915 =
                                             FStar_Syntax_Subst.compress
                                               lb1.FStar_Syntax_Syntax.lbtyp
                                              in
                                           uu____3915.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____3914 with
                                          | FStar_Syntax_Syntax.Tm_unknown 
                                              -> true
                                          | uu____3920 -> false)
                                     | uu____3922 ->
                                         failwith
                                           "Impossible: first phase lb and second phase lb differ in structure!"
                                      in
                                   if lb_unannotated
                                   then
                                     let uu___686_3926 = e_lax  in
                                     {
                                       FStar_Syntax_Syntax.n =
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((false,
                                               [(let uu___688_3941 = lb  in
                                                 {
                                                   FStar_Syntax_Syntax.lbname
                                                     =
                                                     (uu___688_3941.FStar_Syntax_Syntax.lbname);
                                                   FStar_Syntax_Syntax.lbunivs
                                                     =
                                                     (uu___688_3941.FStar_Syntax_Syntax.lbunivs);
                                                   FStar_Syntax_Syntax.lbtyp
                                                     =
                                                     FStar_Syntax_Syntax.tun;
                                                   FStar_Syntax_Syntax.lbeff
                                                     =
                                                     (uu___688_3941.FStar_Syntax_Syntax.lbeff);
                                                   FStar_Syntax_Syntax.lbdef
                                                     =
                                                     (uu___688_3941.FStar_Syntax_Syntax.lbdef);
                                                   FStar_Syntax_Syntax.lbattrs
                                                     =
                                                     (uu___688_3941.FStar_Syntax_Syntax.lbattrs);
                                                   FStar_Syntax_Syntax.lbpos
                                                     =
                                                     (uu___688_3941.FStar_Syntax_Syntax.lbpos)
                                                 })]), e2));
                                       FStar_Syntax_Syntax.pos =
                                         (uu___686_3926.FStar_Syntax_Syntax.pos);
                                       FStar_Syntax_Syntax.vars =
                                         (uu___686_3926.FStar_Syntax_Syntax.vars)
                                     }
                                   else e_lax
                               | uu____3944 -> e_lax  in
                             let uu____3945 =
                               FStar_Util.record_time
                                 (fun uu____3953  ->
                                    let uu____3954 =
                                      let uu____3955 =
                                        let uu____3956 =
                                          FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                            (let uu___692_3965 = env'  in
                                             {
                                               FStar_TypeChecker_Env.solver =
                                                 (uu___692_3965.FStar_TypeChecker_Env.solver);
                                               FStar_TypeChecker_Env.range =
                                                 (uu___692_3965.FStar_TypeChecker_Env.range);
                                               FStar_TypeChecker_Env.curmodule
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.curmodule);
                                               FStar_TypeChecker_Env.gamma =
                                                 (uu___692_3965.FStar_TypeChecker_Env.gamma);
                                               FStar_TypeChecker_Env.gamma_sig
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.gamma_sig);
                                               FStar_TypeChecker_Env.gamma_cache
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.gamma_cache);
                                               FStar_TypeChecker_Env.modules
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.modules);
                                               FStar_TypeChecker_Env.expected_typ
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.expected_typ);
                                               FStar_TypeChecker_Env.sigtab =
                                                 (uu___692_3965.FStar_TypeChecker_Env.sigtab);
                                               FStar_TypeChecker_Env.attrtab
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.attrtab);
                                               FStar_TypeChecker_Env.instantiate_imp
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.instantiate_imp);
                                               FStar_TypeChecker_Env.effects
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.effects);
                                               FStar_TypeChecker_Env.generalize
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.generalize);
                                               FStar_TypeChecker_Env.letrecs
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.letrecs);
                                               FStar_TypeChecker_Env.top_level
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.top_level);
                                               FStar_TypeChecker_Env.check_uvars
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.check_uvars);
                                               FStar_TypeChecker_Env.use_eq =
                                                 (uu___692_3965.FStar_TypeChecker_Env.use_eq);
                                               FStar_TypeChecker_Env.use_eq_strict
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.use_eq_strict);
                                               FStar_TypeChecker_Env.is_iface
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.is_iface);
                                               FStar_TypeChecker_Env.admit =
                                                 (uu___692_3965.FStar_TypeChecker_Env.admit);
                                               FStar_TypeChecker_Env.lax =
                                                 true;
                                               FStar_TypeChecker_Env.lax_universes
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.lax_universes);
                                               FStar_TypeChecker_Env.phase1 =
                                                 true;
                                               FStar_TypeChecker_Env.failhard
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.failhard);
                                               FStar_TypeChecker_Env.nosynth
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.nosynth);
                                               FStar_TypeChecker_Env.uvar_subtyping
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.uvar_subtyping);
                                               FStar_TypeChecker_Env.tc_term
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.tc_term);
                                               FStar_TypeChecker_Env.type_of
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.type_of);
                                               FStar_TypeChecker_Env.universe_of
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.universe_of);
                                               FStar_TypeChecker_Env.check_type_of
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.check_type_of);
                                               FStar_TypeChecker_Env.use_bv_sorts
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.use_bv_sorts);
                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.qtbl_name_and_index);
                                               FStar_TypeChecker_Env.normalized_eff_names
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.normalized_eff_names);
                                               FStar_TypeChecker_Env.fv_delta_depths
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.fv_delta_depths);
                                               FStar_TypeChecker_Env.proof_ns
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.proof_ns);
                                               FStar_TypeChecker_Env.synth_hook
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.synth_hook);
                                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                               FStar_TypeChecker_Env.splice =
                                                 (uu___692_3965.FStar_TypeChecker_Env.splice);
                                               FStar_TypeChecker_Env.mpreprocess
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.mpreprocess);
                                               FStar_TypeChecker_Env.postprocess
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.postprocess);
                                               FStar_TypeChecker_Env.identifier_info
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.identifier_info);
                                               FStar_TypeChecker_Env.tc_hooks
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.tc_hooks);
                                               FStar_TypeChecker_Env.dsenv =
                                                 (uu___692_3965.FStar_TypeChecker_Env.dsenv);
                                               FStar_TypeChecker_Env.nbe =
                                                 (uu___692_3965.FStar_TypeChecker_Env.nbe);
                                               FStar_TypeChecker_Env.strict_args_tab
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.strict_args_tab);
                                               FStar_TypeChecker_Env.erasable_types_tab
                                                 =
                                                 (uu___692_3965.FStar_TypeChecker_Env.erasable_types_tab)
                                             }) e
                                           in
                                        FStar_All.pipe_right uu____3956
                                          (fun uu____3978  ->
                                             match uu____3978 with
                                             | (e1,uu____3986,uu____3987) ->
                                                 e1)
                                         in
                                      FStar_All.pipe_right uu____3955
                                        (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                           env')
                                       in
                                    FStar_All.pipe_right uu____3954
                                      drop_lbtyp)
                                in
                             match uu____3945 with
                             | (e1,ms) ->
                                 ((let uu____3993 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env1)
                                       (FStar_Options.Other "TwoPhases")
                                      in
                                   if uu____3993
                                   then
                                     let uu____3998 =
                                       FStar_Syntax_Print.term_to_string e1
                                        in
                                     FStar_Util.print1
                                       "Let binding after phase 1: %s\n"
                                       uu____3998
                                   else ());
                                  (let uu____4004 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env1)
                                       (FStar_Options.Other "TCDeclTime")
                                      in
                                   if uu____4004
                                   then
                                     let uu____4009 =
                                       FStar_Util.string_of_int ms  in
                                     FStar_Util.print1
                                       "Let binding elaborated (phase 1) in %s milliseconds\n"
                                       uu____4009
                                   else ());
                                  e1)
                           else e  in
                         let uu____4016 =
                           let uu____4025 =
                             FStar_Syntax_Util.extract_attr'
                               FStar_Parser_Const.postprocess_with
                               se2.FStar_Syntax_Syntax.sigattrs
                              in
                           match uu____4025 with
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
                         (match uu____4016 with
                          | (attrs1,post_tau) ->
                              let se3 =
                                let uu___722_4130 = se2  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___722_4130.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___722_4130.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___722_4130.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___722_4130.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs = attrs1;
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___722_4130.FStar_Syntax_Syntax.sigopts)
                                }  in
                              let postprocess_lb tau lb =
                                let lbdef =
                                  FStar_TypeChecker_Env.postprocess env1 tau
                                    lb.FStar_Syntax_Syntax.lbtyp
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                let uu___729_4143 = lb  in
                                {
                                  FStar_Syntax_Syntax.lbname =
                                    (uu___729_4143.FStar_Syntax_Syntax.lbname);
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___729_4143.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp =
                                    (uu___729_4143.FStar_Syntax_Syntax.lbtyp);
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___729_4143.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = lbdef;
                                  FStar_Syntax_Syntax.lbattrs =
                                    (uu___729_4143.FStar_Syntax_Syntax.lbattrs);
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___729_4143.FStar_Syntax_Syntax.lbpos)
                                }  in
                              let uu____4144 =
                                FStar_Util.record_time
                                  (fun uu____4163  ->
                                     FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                       env' e1)
                                 in
                              (match uu____4144 with
                               | (r1,ms) ->
                                   ((let uu____4191 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "TCDeclTime")
                                        in
                                     if uu____4191
                                     then
                                       let uu____4196 =
                                         FStar_Util.string_of_int ms  in
                                       FStar_Util.print1
                                         "Let binding typechecked in phase 2 in %s milliseconds\n"
                                         uu____4196
                                     else ());
                                    (let uu____4201 =
                                       match r1 with
                                       | ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_let
                                              (lbs1,e2);
                                            FStar_Syntax_Syntax.pos =
                                              uu____4226;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4227;_},uu____4228,g)
                                           when
                                           FStar_TypeChecker_Env.is_trivial g
                                           ->
                                           let lbs2 =
                                             let uu____4258 =
                                               FStar_All.pipe_right
                                                 (FStar_Pervasives_Native.snd
                                                    lbs1)
                                                 (FStar_List.map
                                                    rename_parameters)
                                                in
                                             ((FStar_Pervasives_Native.fst
                                                 lbs1), uu____4258)
                                              in
                                           let lbs3 =
                                             let uu____4282 =
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
                                                 lbs2), uu____4282)
                                              in
                                           let quals1 =
                                             match e2.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_meta
                                                 (uu____4305,FStar_Syntax_Syntax.Meta_desugared
                                                  (FStar_Syntax_Syntax.Masked_effect
                                                  ))
                                                 ->
                                                 FStar_Syntax_Syntax.HasMaskedEffect
                                                 :: quals
                                             | uu____4310 -> quals  in
                                           ((let uu___759_4319 = se3  in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_let
                                                    (lbs3, lids));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___759_4319.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 quals1;
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___759_4319.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___759_4319.FStar_Syntax_Syntax.sigattrs);
                                               FStar_Syntax_Syntax.sigopts =
                                                 (uu___759_4319.FStar_Syntax_Syntax.sigopts)
                                             }), lbs3)
                                       | uu____4322 ->
                                           failwith
                                             "impossible (typechecking should preserve Tm_let)"
                                        in
                                     match uu____4201 with
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
                                          (let uu____4378 = log env1  in
                                           if uu____4378
                                           then
                                             let uu____4381 =
                                               let uu____4383 =
                                                 FStar_All.pipe_right
                                                   (FStar_Pervasives_Native.snd
                                                      lbs1)
                                                   (FStar_List.map
                                                      (fun lb  ->
                                                         let should_log =
                                                           let uu____4403 =
                                                             let uu____4412 =
                                                               let uu____4413
                                                                 =
                                                                 let uu____4416
                                                                   =
                                                                   FStar_Util.right
                                                                    lb.FStar_Syntax_Syntax.lbname
                                                                    in
                                                                 uu____4416.FStar_Syntax_Syntax.fv_name
                                                                  in
                                                               uu____4413.FStar_Syntax_Syntax.v
                                                                in
                                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                                               env1
                                                               uu____4412
                                                              in
                                                           match uu____4403
                                                           with
                                                           | FStar_Pervasives_Native.None
                                                                -> true
                                                           | uu____4425 ->
                                                               false
                                                            in
                                                         if should_log
                                                         then
                                                           let uu____4437 =
                                                             FStar_Syntax_Print.lbname_to_string
                                                               lb.FStar_Syntax_Syntax.lbname
                                                              in
                                                           let uu____4439 =
                                                             FStar_Syntax_Print.term_to_string
                                                               lb.FStar_Syntax_Syntax.lbtyp
                                                              in
                                                           FStar_Util.format2
                                                             "let %s : %s"
                                                             uu____4437
                                                             uu____4439
                                                         else ""))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____4383
                                                 (FStar_String.concat "\n")
                                                in
                                             FStar_Util.print1 "%s\n"
                                               uu____4381
                                           else ());
                                          check_must_erase_attribute env0 se4;
                                          ([se4], [], env0))))))))
           | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n,p,t,uu____4462) ->
               let t1 =
                 let uu____4464 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env)
                    in
                 if uu____4464
                 then
                   let uu____4467 =
                     let uu____4472 =
                       let uu____4473 =
                         let uu____4474 =
                           FStar_TypeChecker_TcEffect.tc_polymonadic_bind
                             (let uu___784_4481 = env  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___784_4481.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___784_4481.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___784_4481.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___784_4481.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___784_4481.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___784_4481.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___784_4481.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___784_4481.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___784_4481.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___784_4481.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___784_4481.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___784_4481.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___784_4481.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___784_4481.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___784_4481.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___784_4481.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___784_4481.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (uu___784_4481.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___784_4481.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___784_4481.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___784_4481.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___784_4481.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___784_4481.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___784_4481.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___784_4481.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___784_4481.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___784_4481.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___784_4481.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___784_4481.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___784_4481.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___784_4481.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___784_4481.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___784_4481.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___784_4481.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___784_4481.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___784_4481.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (uu___784_4481.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___784_4481.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___784_4481.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___784_4481.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___784_4481.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___784_4481.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___784_4481.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___784_4481.FStar_TypeChecker_Env.erasable_types_tab)
                              }) m n p t
                            in
                         FStar_All.pipe_right uu____4474
                           (fun uu____4492  ->
                              match uu____4492 with
                              | (t1,ty) ->
                                  let uu___789_4499 = se1  in
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (FStar_Syntax_Syntax.Sig_polymonadic_bind
                                         (m, n, p, t1, ty));
                                    FStar_Syntax_Syntax.sigrng =
                                      (uu___789_4499.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals =
                                      (uu___789_4499.FStar_Syntax_Syntax.sigquals);
                                    FStar_Syntax_Syntax.sigmeta =
                                      (uu___789_4499.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (uu___789_4499.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (uu___789_4499.FStar_Syntax_Syntax.sigopts)
                                  })
                          in
                       FStar_All.pipe_right uu____4473
                         (FStar_TypeChecker_Normalize.elim_uvars env)
                        in
                     FStar_All.pipe_right uu____4472
                       (fun se2  ->
                          match se2.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_polymonadic_bind
                              (uu____4515,uu____4516,uu____4517,t1,ty) ->
                              (t1, ty)
                          | uu____4520 ->
                              failwith
                                "Impossible! tc for Sig_polymonadic_bind must be a Sig_polymonadic_bind")
                      in
                   match uu____4467 with
                   | (t1,ty) ->
                       ((let uu____4529 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "TwoPhases")
                            in
                         if uu____4529
                         then
                           let uu____4534 =
                             FStar_Syntax_Print.sigelt_to_string
                               (let uu___804_4538 = se1  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_polymonadic_bind
                                       (m, n, p, t1, ty));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___804_4538.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___804_4538.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___804_4538.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___804_4538.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___804_4538.FStar_Syntax_Syntax.sigopts)
                                })
                              in
                           FStar_Util.print1
                             "Polymonadic bind after phase 1: %s\n"
                             uu____4534
                         else ());
                        t1)
                 else t  in
               let uu____4544 =
                 FStar_TypeChecker_TcEffect.tc_polymonadic_bind env m n p t1
                  in
               (match uu____4544 with
                | (t2,ty) ->
                    let se2 =
                      let uu___811_4562 = se1  in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_polymonadic_bind
                             (m, n, p, t2, ty));
                        FStar_Syntax_Syntax.sigrng =
                          (uu___811_4562.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___811_4562.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___811_4562.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___811_4562.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___811_4562.FStar_Syntax_Syntax.sigopts)
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
      let uu____4598 =
        env.FStar_TypeChecker_Env.nosynth && (FStar_Options.debug_any ())  in
      if uu____4598
      then ([], [], env)
      else
        (let env1 = set_hint_correlator env se  in
         (let uu____4619 =
            let uu____4621 =
              FStar_Ident.string_of_lid env1.FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____4621  in
          if uu____4619
          then
            let uu____4624 =
              let uu____4626 =
                FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                  (FStar_List.map FStar_Ident.string_of_lid)
                 in
              FStar_All.pipe_right uu____4626 (FStar_String.concat ", ")  in
            FStar_Util.print1 "Processing %s\n" uu____4624
          else ());
         (let uu____4645 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
             in
          if uu____4645
          then
            let uu____4648 = FStar_Syntax_Print.sigelt_to_string se  in
            FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____4648
          else ());
         if
           (se.FStar_Syntax_Syntax.sigmeta).FStar_Syntax_Syntax.sigmeta_admit
         then
           (let old = FStar_Options.admit_smt_queries ()  in
            FStar_Options.set_admit_smt_queries true;
            (let result = tc_decl' env1 se  in
             FStar_Options.set_admit_smt_queries old; result))
         else tc_decl' env1 se)
  
let for_export :
  'uuuuuu4691 .
    'uuuuuu4691 ->
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
               (fun uu___2_4734  ->
                  match uu___2_4734 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____4737 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____4748) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____4756 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____4766 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_fail uu____4771 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_splice uu____4793 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____4809 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____4835 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4861) ->
            let uu____4870 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____4870
            then
              let for_export_bundle se1 uu____4907 =
                match uu____4907 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____4946,uu____4947) ->
                         let dec =
                           let uu___871_4957 = se1  in
                           let uu____4958 =
                             let uu____4959 =
                               let uu____4966 =
                                 let uu____4967 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____4967  in
                               (l, us, uu____4966)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____4959
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____4958;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___871_4957.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___871_4957.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___871_4957.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___871_4957.FStar_Syntax_Syntax.sigopts)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____4977,uu____4978,uu____4979) ->
                         let dec =
                           let uu___882_4987 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___882_4987.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___882_4987.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___882_4987.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___882_4987.FStar_Syntax_Syntax.sigopts)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____4992 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume (uu____5015,uu____5016,uu____5017)
            ->
            let uu____5018 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____5018 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____5042 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____5042
            then
              ([(let uu___898_5061 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___898_5061.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___898_5061.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___898_5061.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (uu___898_5061.FStar_Syntax_Syntax.sigopts)
                 })], (l :: hidden))
            else
              (let uu____5064 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___3_5070  ->
                         match uu___3_5070 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____5073 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____5079 ->
                             true
                         | uu____5081 -> false))
                  in
               if uu____5064 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____5102 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____5107 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____5112 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____5117 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5134 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____5150) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____5164 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____5164
            then ([], hidden)
            else
              (let dec =
                 let uu____5185 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____5185;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = [];
                   FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____5196 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____5196
            then
              let uu____5207 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___935_5221 = se  in
                        let uu____5222 =
                          let uu____5223 =
                            let uu____5230 =
                              let uu____5231 =
                                let uu____5234 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____5234.FStar_Syntax_Syntax.fv_name  in
                              uu____5231.FStar_Syntax_Syntax.v  in
                            (uu____5230, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____5223  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____5222;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___935_5221.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___935_5221.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___935_5221.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___935_5221.FStar_Syntax_Syntax.sigopts)
                        }))
                 in
              (uu____5207, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> Prims.bool -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      fun from_cache  ->
        (let uu____5264 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____5264
         then
           let uu____5267 = FStar_Syntax_Print.sigelt_to_string se  in
           let uu____5269 = FStar_Util.string_of_bool from_cache  in
           FStar_Util.print2
             ">>>>>>>>>>>>>>Adding top-level decl to environment: %s (from_cache:%s)\n"
             uu____5267 uu____5269
         else ());
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____5274 ->
             let uu____5291 =
               let uu____5297 =
                 let uu____5299 = FStar_Syntax_Print.sigelt_to_string se  in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____5299
                  in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____5297)  in
             FStar_Errors.raise_error uu____5291
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_datacon uu____5303 ->
             let uu____5319 =
               let uu____5325 =
                 let uu____5327 = FStar_Syntax_Print.sigelt_to_string se  in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____5327
                  in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____5325)  in
             FStar_Errors.raise_error uu____5319
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_declare_typ
             (uu____5331,uu____5332,uu____5333) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___4_5338  ->
                     match uu___4_5338 with
                     | FStar_Syntax_Syntax.OnlyName  -> true
                     | uu____5341 -> false))
             -> env
         | FStar_Syntax_Syntax.Sig_let (uu____5343,uu____5344) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___4_5353  ->
                     match uu___4_5353 with
                     | FStar_Syntax_Syntax.OnlyName  -> true
                     | uu____5356 -> false))
             -> env
         | uu____5358 ->
             let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PushOptions uu____5360) ->
                  if from_cache
                  then env1
                  else
                    (let uu___972_5367 = env1  in
                     let uu____5368 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___972_5367.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___972_5367.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___972_5367.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___972_5367.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___972_5367.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___972_5367.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___972_5367.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___972_5367.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___972_5367.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___972_5367.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___972_5367.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___972_5367.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___972_5367.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___972_5367.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___972_5367.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___972_5367.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___972_5367.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___972_5367.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___972_5367.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___972_5367.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___972_5367.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___972_5367.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___972_5367.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___972_5367.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___972_5367.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___972_5367.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___972_5367.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___972_5367.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___972_5367.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___972_5367.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___972_5367.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___972_5367.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___972_5367.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___972_5367.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5368;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___972_5367.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___972_5367.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___972_5367.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___972_5367.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___972_5367.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___972_5367.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___972_5367.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___972_5367.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___972_5367.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___972_5367.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___972_5367.FStar_TypeChecker_Env.erasable_types_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PopOptions ) ->
                  if from_cache
                  then env1
                  else
                    (let uu___972_5372 = env1  in
                     let uu____5373 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___972_5372.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___972_5372.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___972_5372.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___972_5372.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___972_5372.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___972_5372.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___972_5372.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___972_5372.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___972_5372.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___972_5372.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___972_5372.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___972_5372.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___972_5372.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___972_5372.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___972_5372.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___972_5372.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___972_5372.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___972_5372.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___972_5372.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___972_5372.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___972_5372.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___972_5372.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___972_5372.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___972_5372.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___972_5372.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___972_5372.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___972_5372.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___972_5372.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___972_5372.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___972_5372.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___972_5372.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___972_5372.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___972_5372.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___972_5372.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5373;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___972_5372.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___972_5372.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___972_5372.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___972_5372.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___972_5372.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___972_5372.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___972_5372.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___972_5372.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___972_5372.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___972_5372.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___972_5372.FStar_TypeChecker_Env.erasable_types_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.SetOptions uu____5374) ->
                  if from_cache
                  then env1
                  else
                    (let uu___972_5379 = env1  in
                     let uu____5380 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___972_5379.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___972_5379.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___972_5379.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___972_5379.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___972_5379.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___972_5379.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___972_5379.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___972_5379.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___972_5379.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___972_5379.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___972_5379.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___972_5379.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___972_5379.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___972_5379.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___972_5379.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___972_5379.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___972_5379.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___972_5379.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___972_5379.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___972_5379.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___972_5379.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___972_5379.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___972_5379.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___972_5379.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___972_5379.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___972_5379.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___972_5379.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___972_5379.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___972_5379.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___972_5379.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___972_5379.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___972_5379.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___972_5379.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___972_5379.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5380;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___972_5379.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___972_5379.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___972_5379.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___972_5379.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___972_5379.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___972_5379.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___972_5379.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___972_5379.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___972_5379.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___972_5379.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___972_5379.FStar_TypeChecker_Env.erasable_types_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.ResetOptions uu____5381) ->
                  if from_cache
                  then env1
                  else
                    (let uu___972_5388 = env1  in
                     let uu____5389 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___972_5388.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___972_5388.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___972_5388.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___972_5388.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___972_5388.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___972_5388.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___972_5388.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___972_5388.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___972_5388.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___972_5388.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___972_5388.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___972_5388.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___972_5388.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___972_5388.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___972_5388.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___972_5388.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___972_5388.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___972_5388.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___972_5388.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___972_5388.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___972_5388.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___972_5388.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___972_5388.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___972_5388.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___972_5388.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___972_5388.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___972_5388.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___972_5388.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___972_5388.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___972_5388.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___972_5388.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___972_5388.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___972_5388.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___972_5388.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5389;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___972_5388.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___972_5388.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___972_5388.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___972_5388.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___972_5388.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___972_5388.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___972_5388.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___972_5388.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___972_5388.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___972_5388.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___972_5388.FStar_TypeChecker_Env.erasable_types_tab)
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
                            let uu____5405 =
                              FStar_Syntax_Util.action_as_lb
                                ne.FStar_Syntax_Syntax.mname a
                                (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Env.push_sigelt env3 uu____5405)
                       env2)
              | FStar_Syntax_Syntax.Sig_sub_effect sub ->
                  FStar_TypeChecker_Util.update_env_sub_eff env1 sub
              | FStar_Syntax_Syntax.Sig_polymonadic_bind
                  (m,n,p,uu____5410,ty) ->
                  FStar_TypeChecker_Util.update_env_polymonadic_bind env1 m n
                    p ty
              | uu____5412 -> env1))
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____5481 se =
        match uu____5481 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____5534 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____5534
              then
                let uu____5537 = FStar_Syntax_Print.tag_of_sigelt se  in
                let uu____5539 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print2
                  ">>>>>>>>>>>>>>Checking top-level %s decl %s\n" uu____5537
                  uu____5539
              else ());
             (let uu____5544 = tc_decl env1 se  in
              match uu____5544 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____5597 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____5597
                             then
                               let uu____5601 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____5601
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____5617 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____5617
                             then
                               let uu____5621 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\n"
                                 uu____5621
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
                    (let uu____5639 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____5639
                     then
                       let uu____5644 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____5653 =
                                  let uu____5655 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____5655 "\n"  in
                                Prims.op_Hat s uu____5653) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____5644
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____5665 =
                       let uu____5674 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____5674
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____5716 se1 =
                            match uu____5716 with
                            | (exports1,hidden1) ->
                                let uu____5744 = for_export env3 hidden1 se1
                                   in
                                (match uu____5744 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____5665 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____5898 = acc  in
        match uu____5898 with
        | (uu____5933,uu____5934,env1,uu____5936) ->
            let r =
              let uu____5970 =
                let uu____5974 =
                  let uu____5976 = FStar_TypeChecker_Env.current_module env1
                     in
                  FStar_Ident.string_of_lid uu____5976  in
                FStar_Pervasives_Native.Some uu____5974  in
              FStar_Profiling.profile
                (fun uu____5999  -> process_one_decl acc se) uu____5970
                "FStar.TypeChecker.Tc.process_one_decl"
               in
            ((let uu____6002 = FStar_Options.profile_group_by_decls ()  in
              if uu____6002
              then
                let tag =
                  match FStar_Syntax_Util.lids_of_sigelt se with
                  | hd::uu____6009 -> FStar_Ident.string_of_lid hd
                  | uu____6012 ->
                      FStar_Range.string_of_range
                        (FStar_Syntax_Util.range_of_sigelt se)
                   in
                FStar_Profiling.report_and_clear tag
              else ());
             r)
         in
      let uu____6017 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____6017 with
      | (ses1,exports,env1,uu____6065) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
  
let (uu___1062 : unit) =
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
          let uu___1066_6181 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1066_6181.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1066_6181.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1066_6181.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1066_6181.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1066_6181.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1066_6181.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1066_6181.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1066_6181.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1066_6181.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1066_6181.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1066_6181.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1066_6181.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1066_6181.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1066_6181.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___1066_6181.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1066_6181.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1066_6181.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1066_6181.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1066_6181.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___1066_6181.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1066_6181.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1066_6181.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1066_6181.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1066_6181.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1066_6181.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1066_6181.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1066_6181.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1066_6181.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1066_6181.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1066_6181.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1066_6181.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1066_6181.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1066_6181.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1066_6181.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1066_6181.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1066_6181.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1066_6181.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1066_6181.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1066_6181.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1066_6181.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1066_6181.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1066_6181.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1066_6181.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        let check_term lid univs t =
          let uu____6201 = FStar_Syntax_Subst.open_univ_vars univs t  in
          match uu____6201 with
          | (univs1,t1) ->
              ((let uu____6209 =
                  let uu____6211 =
                    let uu____6217 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____6217  in
                  FStar_All.pipe_left uu____6211
                    (FStar_Options.Other "Exports")
                   in
                if uu____6209
                then
                  let uu____6221 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____6223 =
                    let uu____6225 =
                      FStar_All.pipe_right univs1
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____6225
                      (FStar_String.concat ", ")
                     in
                  let uu____6242 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____6221 uu____6223 uu____6242
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs1
                   in
                let uu____6248 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____6248 (fun uu____6257  -> ())))
           in
        let check_term1 lid univs t =
          (let uu____6275 =
             let uu____6277 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____6279 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____6277 uu____6279
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____6275);
          check_term lid univs t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6290) ->
              let uu____6299 =
                let uu____6301 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6301  in
              if uu____6299
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs,binders,typ,uu____6315,uu____6316) ->
              let t =
                let uu____6328 =
                  let uu____6335 =
                    let uu____6336 =
                      let uu____6351 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____6351)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____6336  in
                  FStar_Syntax_Syntax.mk uu____6335  in
                uu____6328 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs,t,uu____6367,uu____6368,uu____6369) ->
              check_term1 l univs t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs,t) ->
              let uu____6379 =
                let uu____6381 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6381  in
              if uu____6379 then check_term1 l univs t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____6389,lbs),uu____6391) ->
              let uu____6402 =
                let uu____6404 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6404  in
              if uu____6402
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
              let uu____6427 =
                let uu____6429 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6429  in
              if uu____6427
              then
                let arrow =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs arrow
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____6450 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____6451 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____6458 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____6459 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____6460 -> ()
          | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____6461 -> ()
          | FStar_Syntax_Syntax.Sig_fail uu____6472 ->
              failwith "Impossible (Already handled)"
          | FStar_Syntax_Syntax.Sig_splice uu____6486 ->
              failwith "Impossible (Already handled)"
           in
        let uu____6494 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____6494 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____6600) -> true
             | uu____6602 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____6632 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____6671 ->
                   let uu____6672 =
                     let uu____6679 =
                       let uu____6680 =
                         let uu____6695 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____6695)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____6680  in
                     FStar_Syntax_Syntax.mk uu____6679  in
                   uu____6672 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____6712,uu____6713) ->
            let s1 =
              let uu___1194_6723 = s  in
              let uu____6724 =
                let uu____6725 =
                  let uu____6732 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____6732)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____6725  in
              let uu____6733 =
                let uu____6736 =
                  let uu____6739 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____6739  in
                FStar_Syntax_Syntax.Assumption :: uu____6736  in
              {
                FStar_Syntax_Syntax.sigel = uu____6724;
                FStar_Syntax_Syntax.sigrng =
                  (uu___1194_6723.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____6733;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___1194_6723.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___1194_6723.FStar_Syntax_Syntax.sigattrs);
                FStar_Syntax_Syntax.sigopts =
                  (uu___1194_6723.FStar_Syntax_Syntax.sigopts)
              }  in
            [s1]
        | uu____6742 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____6767 lbdef =
        match uu____6767 with
        | (uvs,t) ->
            let attrs =
              let uu____6778 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____6778
              then
                let uu____6783 =
                  let uu____6784 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____6784
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____6783 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___1207_6787 = s  in
            let uu____6788 =
              let uu____6791 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____6791  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___1207_6787.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____6788;
              FStar_Syntax_Syntax.sigmeta =
                (uu___1207_6787.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs;
              FStar_Syntax_Syntax.sigopts =
                (uu___1207_6787.FStar_Syntax_Syntax.sigopts)
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____6809 -> failwith "Impossible!"  in
        let c_opt =
          let uu____6816 = FStar_Syntax_Util.is_unit t  in
          if uu____6816
          then
            let uu____6823 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____6823
          else
            (let uu____6830 =
               let uu____6831 = FStar_Syntax_Subst.compress t  in
               uu____6831.FStar_Syntax_Syntax.n  in
             match uu____6830 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____6838,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____6862 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____6874 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____6874
            then false
            else
              (let uu____6881 = FStar_Syntax_Util.is_pure_or_ghost_comp c  in
               if uu____6881
               then true
               else
                 (let uu____6888 = comp_effect_name c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____6888))
         in
      let extract_sigelt s =
        (let uu____6900 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____6900
         then
           let uu____6903 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____6903
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____6910 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____6930 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____6949 ->
             failwith
               "Impossible! extract_interface: trying to extract splice"
         | FStar_Syntax_Syntax.Sig_fail uu____6959 ->
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
                             (lid,uu____7011,uu____7012,uu____7013,uu____7014,uu____7015)
                             ->
                             ((let uu____7025 =
                                 let uu____7028 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____7028  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____7025);
                              (let uu____7077 = vals_of_abstract_inductive s1
                                  in
                               FStar_List.append uu____7077 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____7081,uu____7082,uu____7083,uu____7084,uu____7085)
                             ->
                             ((let uu____7093 =
                                 let uu____7096 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____7096  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____7093);
                              sigelts1)
                         | uu____7145 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____7154 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____7154
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____7164 =
                    let uu___1273_7165 = s  in
                    let uu____7166 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1273_7165.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1273_7165.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____7166;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1273_7165.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1273_7165.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1273_7165.FStar_Syntax_Syntax.sigopts)
                    }  in
                  [uu____7164])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____7177 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____7177
             then []
             else
               (let uu____7184 = lbs  in
                match uu____7184 with
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
                        (fun uu____7246  ->
                           match uu____7246 with
                           | (uu____7254,t,uu____7256) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____7273  ->
                             match uu____7273 with
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
                           (fun uu____7300  ->
                              match uu____7300 with
                              | (uu____7308,t,uu____7310) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____7322,uu____7323) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____7331 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____7360 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____7360) uu____7331
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____7364 =
                    let uu___1315_7365 = s  in
                    let uu____7366 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1315_7365.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1315_7365.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____7366;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1315_7365.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1315_7365.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1315_7365.FStar_Syntax_Syntax.sigopts)
                    }  in
                  [uu____7364]
                else [])
             else
               (let uu____7373 =
                  let uu___1317_7374 = s  in
                  let uu____7375 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1317_7374.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1317_7374.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____7375;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1317_7374.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1317_7374.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___1317_7374.FStar_Syntax_Syntax.sigopts)
                  }  in
                [uu____7373])
         | FStar_Syntax_Syntax.Sig_new_effect uu____7378 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____7379 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7380 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____7393 -> [s]
         | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____7394 -> [s])
         in
      let uu___1329_7405 = m  in
      let uu____7406 =
        let uu____7407 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____7407 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___1329_7405.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____7406;
        FStar_Syntax_Syntax.exports =
          (uu___1329_7405.FStar_Syntax_Syntax.exports);
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
        (fun uu____7458  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____7505  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____7520 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____7520
  
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
        let uu____7592 =
          FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
        FStar_Options.should_verify uu____7592  in
      let action = if verify then "Verifying" else "Lax-checking"  in
      let label =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation"  in
      (let uu____7611 = FStar_Options.debug_any ()  in
       if uu____7611
       then
         let uu____7614 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
         FStar_Util.print3 "%s %s of %s\n" action label uu____7614
       else ());
      (let name =
         let uu____7621 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") uu____7621
          in
       let env1 =
         let uu___1354_7631 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___1354_7631.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___1354_7631.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___1354_7631.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___1354_7631.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___1354_7631.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___1354_7631.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___1354_7631.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___1354_7631.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___1354_7631.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___1354_7631.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___1354_7631.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___1354_7631.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___1354_7631.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___1354_7631.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___1354_7631.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___1354_7631.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___1354_7631.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___1354_7631.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___1354_7631.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___1354_7631.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___1354_7631.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___1354_7631.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___1354_7631.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___1354_7631.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___1354_7631.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___1354_7631.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___1354_7631.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___1354_7631.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___1354_7631.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___1354_7631.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___1354_7631.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___1354_7631.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___1354_7631.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___1354_7631.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___1354_7631.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___1354_7631.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___1354_7631.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___1354_7631.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___1354_7631.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___1354_7631.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___1354_7631.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___1354_7631.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___1354_7631.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___1354_7631.FStar_TypeChecker_Env.erasable_types_tab)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____7633 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____7633 with
       | (ses,exports,env3) ->
           ((let uu___1362_7666 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___1362_7666.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___1362_7666.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___1362_7666.FStar_Syntax_Syntax.is_interface)
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
        let uu____7695 = tc_decls env decls  in
        match uu____7695 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___1371_7726 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___1371_7726.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___1371_7726.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___1371_7726.FStar_Syntax_Syntax.is_interface)
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
          let uu____7785 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____7785  in
        let env01 = push_context env0 msg  in
        let uu____7789 = tc_partial_modul env01 m  in
        match uu____7789 with
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
                (let uu____7826 = FStar_Errors.get_err_count ()  in
                 uu____7826 = Prims.int_zero)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____7837 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____7837
                then
                  let uu____7841 =
                    FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                  let uu____7843 =
                    let uu____7845 =
                      let uu____7847 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name
                         in
                      FStar_Options.should_verify uu____7847  in
                    if uu____7845 then "" else " (in lax mode) "  in
                  let uu____7855 =
                    let uu____7857 =
                      let uu____7859 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name
                         in
                      FStar_Options.dump_module uu____7859  in
                    if uu____7857
                    then
                      let uu____7863 =
                        let uu____7865 = FStar_Syntax_Print.modul_to_string m
                           in
                        Prims.op_Hat uu____7865 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____7863
                    else ""  in
                  let uu____7872 =
                    let uu____7874 =
                      let uu____7876 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name
                         in
                      FStar_Options.dump_module uu____7876  in
                    if uu____7874
                    then
                      let uu____7880 =
                        let uu____7882 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____7882 "\n"  in
                      Prims.op_Hat "\nto: " uu____7880
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    uu____7841 uu____7843 uu____7855 uu____7872
                else ());
               (let en0 =
                  let en0 =
                    let uu____7894 =
                      let uu____7896 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name
                         in
                      Prims.op_Hat "Ending modul " uu____7896  in
                    pop_context en uu____7894  in
                  let en01 =
                    let uu___1397_7900 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1397_7900.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1397_7900.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1397_7900.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1397_7900.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1397_7900.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1397_7900.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1397_7900.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1397_7900.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1397_7900.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1397_7900.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1397_7900.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1397_7900.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1397_7900.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1397_7900.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1397_7900.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1397_7900.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1397_7900.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.use_eq_strict =
                        (uu___1397_7900.FStar_TypeChecker_Env.use_eq_strict);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1397_7900.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1397_7900.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1397_7900.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1397_7900.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1397_7900.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1397_7900.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1397_7900.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1397_7900.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1397_7900.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1397_7900.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1397_7900.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1397_7900.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1397_7900.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1397_7900.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1397_7900.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1397_7900.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1397_7900.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1397_7900.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1397_7900.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1397_7900.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.mpreprocess =
                        (uu___1397_7900.FStar_TypeChecker_Env.mpreprocess);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1397_7900.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1397_7900.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1397_7900.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1397_7900.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1397_7900.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___1397_7900.FStar_TypeChecker_Env.erasable_types_tab)
                    }  in
                  let en02 =
                    let uu___1400_7902 = en01  in
                    let uu____7903 =
                      let uu____7918 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____7918, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1400_7902.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1400_7902.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1400_7902.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1400_7902.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1400_7902.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1400_7902.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1400_7902.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1400_7902.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1400_7902.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1400_7902.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1400_7902.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1400_7902.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1400_7902.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1400_7902.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1400_7902.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1400_7902.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1400_7902.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.use_eq_strict =
                        (uu___1400_7902.FStar_TypeChecker_Env.use_eq_strict);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1400_7902.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1400_7902.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1400_7902.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1400_7902.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1400_7902.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1400_7902.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1400_7902.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1400_7902.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1400_7902.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1400_7902.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1400_7902.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1400_7902.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1400_7902.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____7903;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1400_7902.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1400_7902.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1400_7902.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1400_7902.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1400_7902.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1400_7902.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.mpreprocess =
                        (uu___1400_7902.FStar_TypeChecker_Env.mpreprocess);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1400_7902.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1400_7902.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1400_7902.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1400_7902.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1400_7902.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1400_7902.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___1400_7902.FStar_TypeChecker_Env.erasable_types_tab)
                    }  in
                  let uu____7964 =
                    let uu____7966 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____7966  in
                  if uu____7964
                  then
                    ((let uu____7970 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____7970 (fun uu____7972  -> ()));
                     en02)
                  else en02  in
                let uu____7975 = tc_modul en0 modul_iface true  in
                match uu____7975 with
                | (modul_iface1,env) ->
                    ((let uu___1409_7988 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___1409_7988.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___1409_7988.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___1409_7988.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___1411_7992 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___1411_7992.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___1411_7992.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___1411_7992.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____7995 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____7995 FStar_Util.smap_clear);
               (let uu____8031 =
                  ((let uu____8035 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____8035) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____8038 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____8038)
                   in
                if uu____8031 then check_exports env modul exports else ());
               (let uu____8044 =
                  let uu____8045 =
                    let uu____8047 =
                      FStar_Ident.string_of_lid
                        modul.FStar_Syntax_Syntax.name
                       in
                    Prims.op_Hat "Ending modul " uu____8047  in
                  pop_context env uu____8045  in
                FStar_All.pipe_right uu____8044 (fun uu____8050  -> ()));
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
        let uu____8064 =
          let uu____8066 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____8066  in
        push_context env uu____8064  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = add_sigelt_to_env env2 se true  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____8088 =
                         FStar_TypeChecker_Env.lookup_sigelt env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____8091 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____8091 with | (uu____8098,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____8123 = FStar_Options.debug_any ()  in
         if uu____8123
         then
           let uu____8126 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____8126
         else ());
        (let uu____8138 =
           let uu____8140 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Options.dump_module uu____8140  in
         if uu____8138
         then
           let uu____8143 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____8143
         else ());
        (let env1 =
           let uu___1441_8149 = env  in
           let uu____8150 =
             let uu____8152 =
               let uu____8154 =
                 FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
               FStar_Options.should_verify uu____8154  in
             Prims.op_Negation uu____8152  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___1441_8149.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___1441_8149.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___1441_8149.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___1441_8149.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___1441_8149.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___1441_8149.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___1441_8149.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___1441_8149.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___1441_8149.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___1441_8149.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___1441_8149.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___1441_8149.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___1441_8149.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___1441_8149.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___1441_8149.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___1441_8149.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___1441_8149.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.use_eq_strict =
               (uu___1441_8149.FStar_TypeChecker_Env.use_eq_strict);
             FStar_TypeChecker_Env.is_iface =
               (uu___1441_8149.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___1441_8149.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____8150;
             FStar_TypeChecker_Env.lax_universes =
               (uu___1441_8149.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___1441_8149.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___1441_8149.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___1441_8149.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___1441_8149.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___1441_8149.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___1441_8149.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___1441_8149.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___1441_8149.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___1441_8149.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___1441_8149.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___1441_8149.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___1441_8149.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___1441_8149.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___1441_8149.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___1441_8149.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___1441_8149.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (uu___1441_8149.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (uu___1441_8149.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.identifier_info =
               (uu___1441_8149.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___1441_8149.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___1441_8149.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___1441_8149.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___1441_8149.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___1441_8149.FStar_TypeChecker_Env.erasable_types_tab)
           }  in
         let uu____8156 = tc_modul env1 m b  in
         match uu____8156 with
         | (m1,env2) ->
             ((let uu____8168 =
                 let uu____8170 =
                   FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name  in
                 FStar_Options.dump_module uu____8170  in
               if uu____8168
               then
                 let uu____8173 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____8173
               else ());
              (let uu____8179 =
                 (let uu____8183 =
                    FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name  in
                  FStar_Options.dump_module uu____8183) &&
                   (let uu____8186 =
                      FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name
                       in
                    FStar_Options.debug_at_level uu____8186
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____8179
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
                         let uu____8224 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____8224 with
                         | (univnames,e) ->
                             let uu___1463_8231 = lb  in
                             let uu____8232 =
                               let uu____8235 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames
                                  in
                               n uu____8235 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1463_8231.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1463_8231.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1463_8231.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1463_8231.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____8232;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1463_8231.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1463_8231.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___1465_8236 = se  in
                       let uu____8237 =
                         let uu____8238 =
                           let uu____8245 =
                             let uu____8246 = FStar_List.map update lbs  in
                             (b1, uu____8246)  in
                           (uu____8245, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____8238  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____8237;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1465_8236.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1465_8236.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1465_8236.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___1465_8236.FStar_Syntax_Syntax.sigattrs);
                         FStar_Syntax_Syntax.sigopts =
                           (uu___1465_8236.FStar_Syntax_Syntax.sigopts)
                       }
                   | uu____8254 -> se  in
                 let normalized_module =
                   let uu___1469_8256 = m1  in
                   let uu____8257 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___1469_8256.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____8257;
                     FStar_Syntax_Syntax.exports =
                       (uu___1469_8256.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___1469_8256.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____8258 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____8258
               else ());
              (m1, env2)))
  