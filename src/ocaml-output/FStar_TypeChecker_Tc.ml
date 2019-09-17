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
        let n_opt = FStar_Util.smap_try_find tbl lid.FStar_Ident.str  in
        if FStar_Util.is_some n_opt
        then FStar_All.pipe_right n_opt FStar_Util.must
        else Prims.int_zero  in
      let uu____64 = FStar_Options.reuse_hint_for ()  in
      match uu____64 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____72 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.lid_add_suffix uu____72 l  in
          let uu___16_73 = env  in
          let uu____74 =
            let uu____89 =
              let uu____97 = let uu____103 = get_n lid  in (lid, uu____103)
                 in
              FStar_Pervasives_Native.Some uu____97  in
            (tbl, uu____89)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___16_73.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___16_73.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___16_73.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___16_73.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___16_73.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___16_73.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___16_73.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___16_73.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___16_73.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___16_73.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___16_73.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___16_73.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___16_73.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___16_73.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___16_73.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___16_73.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___16_73.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___16_73.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___16_73.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___16_73.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___16_73.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___16_73.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___16_73.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___16_73.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___16_73.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___16_73.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___16_73.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___16_73.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___16_73.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___16_73.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___16_73.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____74;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___16_73.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___16_73.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___16_73.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___16_73.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___16_73.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___16_73.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___16_73.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___16_73.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___16_73.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___16_73.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___16_73.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___16_73.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___16_73.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___16_73.FStar_TypeChecker_Env.erasable_types_tab)
          }
      | FStar_Pervasives_Native.None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          let lid =
            match lids with
            | [] ->
                let uu____126 = FStar_TypeChecker_Env.current_module env  in
                let uu____127 =
                  let uu____129 = FStar_Ident.next_id ()  in
                  FStar_All.pipe_right uu____129 FStar_Util.string_of_int  in
                FStar_Ident.lid_add_suffix uu____126 uu____127
            | l::uu____134 -> l  in
          let uu___25_137 = env  in
          let uu____138 =
            let uu____153 =
              let uu____161 = let uu____167 = get_n lid  in (lid, uu____167)
                 in
              FStar_Pervasives_Native.Some uu____161  in
            (tbl, uu____153)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___25_137.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___25_137.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___25_137.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___25_137.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___25_137.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___25_137.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___25_137.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___25_137.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___25_137.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___25_137.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___25_137.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___25_137.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___25_137.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___25_137.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___25_137.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___25_137.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___25_137.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___25_137.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___25_137.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___25_137.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___25_137.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___25_137.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___25_137.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___25_137.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___25_137.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___25_137.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___25_137.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___25_137.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___25_137.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___25_137.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___25_137.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____138;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___25_137.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___25_137.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___25_137.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___25_137.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___25_137.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___25_137.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___25_137.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___25_137.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___25_137.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___25_137.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___25_137.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___25_137.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___25_137.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___25_137.FStar_TypeChecker_Env.erasable_types_tab)
          }
  
let (log : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____193 =
         let uu____195 = FStar_TypeChecker_Env.current_module env  in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____195  in
       Prims.op_Negation uu____193)
  
let tc_lex_t :
  'Auu____207 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____207 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____242 = FStar_List.hd ses  in
            uu____242.FStar_Syntax_Syntax.sigrng  in
          (match lids with
           | lex_t1::lex_top1::lex_cons::[] when
               ((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid)
                  &&
                  (FStar_Ident.lid_equals lex_top1
                     FStar_Parser_Const.lextop_lid))
                 &&
                 (FStar_Ident.lid_equals lex_cons
                    FStar_Parser_Const.lexcons_lid)
               -> ()
           | uu____247 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____253,[],t,uu____255,uu____256);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____258;
               FStar_Syntax_Syntax.sigattrs = uu____259;_}::{
                                                              FStar_Syntax_Syntax.sigel
                                                                =
                                                                FStar_Syntax_Syntax.Sig_datacon
                                                                (lex_top1,uu____261,_t_top,_lex_t_top,_295,uu____264);
                                                              FStar_Syntax_Syntax.sigrng
                                                                = r1;
                                                              FStar_Syntax_Syntax.sigquals
                                                                = [];
                                                              FStar_Syntax_Syntax.sigmeta
                                                                = uu____266;
                                                              FStar_Syntax_Syntax.sigattrs
                                                                = uu____267;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____269,_t_cons,_lex_t_cons,_303,uu____272);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____274;
                 FStar_Syntax_Syntax.sigattrs = uu____275;_}::[]
               when
               ((_295 = Prims.int_zero) && (_303 = Prims.int_zero)) &&
                 (((FStar_Ident.lid_equals lex_t1
                      FStar_Parser_Const.lex_t_lid)
                     &&
                     (FStar_Ident.lid_equals lex_top1
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
                        (lex_t1, [u], [], t2, [],
                          [FStar_Parser_Const.lextop_lid;
                          FStar_Parser_Const.lexcons_lid]));
                   FStar_Syntax_Syntax.sigrng = r;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let utop =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r1)
                  in
               let lex_top_t =
                 let uu____328 =
                   let uu____335 =
                     let uu____336 =
                       let uu____343 =
                         let uu____346 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____346
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____343, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____336  in
                   FStar_Syntax_Syntax.mk uu____335  in
                 uu____328 FStar_Pervasives_Native.None r1  in
               let lex_top_t1 =
                 FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t  in
               let dc_lextop =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_top1, [utop], lex_top_t1,
                          FStar_Parser_Const.lex_t_lid, Prims.int_zero, []));
                   FStar_Syntax_Syntax.sigrng = r1;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
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
                   let uu____361 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____361
                    in
                 let hd1 =
                   let uu____363 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____363
                    in
                 let tl1 =
                   let uu____365 =
                     let uu____366 =
                       let uu____373 =
                         let uu____374 =
                           let uu____381 =
                             let uu____384 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____384
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____381, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____374  in
                       FStar_Syntax_Syntax.mk uu____373  in
                     uu____366 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____365
                    in
                 let res =
                   let uu____390 =
                     let uu____397 =
                       let uu____398 =
                         let uu____405 =
                           let uu____408 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____408
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____405,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____398  in
                     FStar_Syntax_Syntax.mk uu____397  in
                   uu____390 FStar_Pervasives_Native.None r2  in
                 let uu____411 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____411
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
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let uu____450 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____450;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____455 ->
               let err_msg =
                 let uu____460 =
                   let uu____462 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____462  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____460
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
    fun uu____487  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____487 with
          | (uvs,t) ->
              let uu____500 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____500 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 =
                     let uu____509 =
                       FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term
                         env1 t1 expected_typ1
                        in
                     match uu____509 with
                     | (t2,uu____517,g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                          t2)
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
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
            Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          (let uu____643 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____643
           then
             let uu____646 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____646
           else ());
          (let uu____651 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____651 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____682 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____682 FStar_List.flatten  in
               ((let uu____696 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____699 = FStar_TypeChecker_Env.should_verify env
                         in
                      Prims.op_Negation uu____699)
                    in
                 if uu____696
                 then ()
                 else
                   (let env1 =
                      FStar_TypeChecker_Env.push_sigelt env sig_bndle  in
                    FStar_List.iter
                      (fun ty  ->
                         let b =
                           FStar_TypeChecker_TcInductive.check_positivity ty
                             env1
                            in
                         if Prims.op_Negation b
                         then
                           let uu____715 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____725,uu____726,uu____727,uu____728,uu____729)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____738 -> failwith "Impossible!"  in
                           match uu____715 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Inductive type "
                                      (Prims.op_Hat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____757 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____767,uu____768,ty_lid,uu____770,uu____771)
                               -> (data_lid, ty_lid)
                           | uu____778 -> failwith "Impossible"  in
                         match uu____757 with
                         | (data_lid,ty_lid) ->
                             let uu____786 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____789 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____789)
                                in
                             if uu____786
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Exception "
                                      (Prims.op_Hat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_haseq =
                   let skip_prims_type uu____805 =
                     let lid =
                       let ty = FStar_List.hd tcs  in
                       match ty.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_inductive_typ
                           (lid,uu____810,uu____811,uu____812,uu____813,uu____814)
                           -> lid
                       | uu____823 -> failwith "Impossible"  in
                     FStar_List.existsb
                       (fun s  ->
                          s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                       FStar_TypeChecker_TcInductive.early_prims_inductives
                      in
                   let is_noeq =
                     FStar_List.existsb
                       (fun q  -> q = FStar_Syntax_Syntax.Noeq) quals
                      in
                   let is_erasable uu____840 =
                     let uu____841 =
                       let uu____844 = FStar_List.hd tcs  in
                       uu____844.FStar_Syntax_Syntax.sigattrs  in
                     FStar_Syntax_Util.has_attribute uu____841
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
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
            Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let env1 = FStar_TypeChecker_Env.push env "tc_inductive"  in
          let pop1 uu____925 =
            let uu____926 = FStar_TypeChecker_Env.pop env1 "tc_inductive"  in
            ()  in
          try
            (fun uu___203_936  ->
               match () with
               | () ->
                   let uu____943 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____943 (fun r  -> pop1 (); r)) ()
          with | uu___202_974 -> (pop1 (); FStar_Exn.raise uu___202_974)
  
let (get_fail_se :
  FStar_Syntax_Syntax.sigelt ->
    (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun se  ->
    let comb f1 f2 =
      match (f1, f2) with
      | (FStar_Pervasives_Native.Some (e1,l1),FStar_Pervasives_Native.Some
         (e2,l2)) ->
          FStar_Pervasives_Native.Some
            ((FStar_List.append e1 e2), (l1 || l2))
      | (FStar_Pervasives_Native.Some (e,l),FStar_Pervasives_Native.None ) ->
          FStar_Pervasives_Native.Some (e, l)
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some (e,l)) ->
          FStar_Pervasives_Native.Some (e, l)
      | uu____1290 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____1348 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____1348 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____1373 .
    'Auu____1373 FStar_Pervasives_Native.option -> 'Auu____1373 Prims.list
  =
  fun uu___0_1382  ->
    match uu___0_1382 with
    | FStar_Pervasives_Native.None  -> []
    | FStar_Pervasives_Native.Some x -> [x]
  
let (check_multi_eq :
  Prims.int Prims.list ->
    Prims.int Prims.list ->
      (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option)
  =
  fun l1  ->
    fun l2  ->
      let rec collect1 l =
        match l with
        | [] -> []
        | hd1::tl1 ->
            let uu____1462 = collect1 tl1  in
            (match uu____1462 with
             | [] -> [(hd1, Prims.int_one)]
             | (h,n1)::t ->
                 if h = hd1
                 then (h, (n1 + Prims.int_one)) :: t
                 else (hd1, Prims.int_one) :: (h, n1) :: t)
         in
      let summ l = collect1 l  in
      let l11 = summ l1  in
      let l21 = summ l2  in
      let rec aux l12 l22 =
        match (l12, l22) with
        | ([],[]) -> FStar_Pervasives_Native.None
        | ((e,n1)::uu____1700,[]) ->
            FStar_Pervasives_Native.Some (e, n1, Prims.int_zero)
        | ([],(e,n1)::uu____1756) ->
            FStar_Pervasives_Native.Some (e, Prims.int_zero, n1)
        | ((hd1,n1)::tl1,(hd2,n2)::tl2) ->
            if hd1 < hd2
            then FStar_Pervasives_Native.Some (hd1, n1, Prims.int_zero)
            else
              if hd1 > hd2
              then FStar_Pervasives_Native.Some (hd2, Prims.int_zero, n2)
              else
                if n1 <> n2
                then FStar_Pervasives_Native.Some (hd1, n1, n2)
                else aux tl1 tl2
         in
      aux l11 l21
  
let (check_must_erase_attribute :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
          let uu____1966 =
            let uu____1968 = FStar_Options.ide ()  in
            Prims.op_Negation uu____1968  in
          if uu____1966
          then
            let uu____1971 =
              let uu____1976 = FStar_TypeChecker_Env.dsenv env  in
              let uu____1977 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____1976 uu____1977  in
            (match uu____1971 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some iface_decls1 ->
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.iter
                      (fun lb  ->
                         let lbname =
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                         let has_iface_val =
                           FStar_All.pipe_right iface_decls1
                             (FStar_Util.for_some
                                (FStar_Parser_AST.decl_is_val
                                   ((lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident))
                            in
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
                              let uu____2010 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____2011 =
                                let uu____2017 =
                                  let uu____2019 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____2021 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____2019 uu____2021
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____2017)
                                 in
                              FStar_Errors.log_issue uu____2010 uu____2011
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____2028 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____2029 =
                                   let uu____2035 =
                                     let uu____2037 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____2037
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____2035)
                                    in
                                 FStar_Errors.log_issue uu____2028 uu____2029)
                              else ())
                         else ())))
          else ()
      | uu____2047 -> ()
  
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
      (let r = se.FStar_Syntax_Syntax.sigrng  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____2092 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____2120 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Parser_Const.lex_t_lid))
           ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let se1 = tc_lex_t env1 ses se.FStar_Syntax_Syntax.sigquals lids
              in
           ([se1], [], env0)
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let ses1 =
             FStar_All.pipe_right ses
               (FStar_List.map
                  (fun e  ->
                     let uu___335_2187 = e  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___335_2187.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___335_2187.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___335_2187.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___335_2187.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (FStar_List.append e.FStar_Syntax_Syntax.sigattrs
                            se.FStar_Syntax_Syntax.sigattrs)
                     }))
              in
           let ses2 =
             let uu____2191 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____2191
             then
               let ses2 =
                 let uu____2199 =
                   let uu____2200 =
                     let uu____2201 =
                       tc_inductive
                         (let uu___339_2210 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___339_2210.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___339_2210.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___339_2210.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___339_2210.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___339_2210.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___339_2210.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___339_2210.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___339_2210.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___339_2210.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___339_2210.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___339_2210.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___339_2210.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___339_2210.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___339_2210.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___339_2210.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___339_2210.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___339_2210.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___339_2210.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___339_2210.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___339_2210.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___339_2210.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___339_2210.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___339_2210.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___339_2210.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___339_2210.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___339_2210.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___339_2210.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___339_2210.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___339_2210.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___339_2210.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___339_2210.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___339_2210.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___339_2210.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___339_2210.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___339_2210.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___339_2210.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___339_2210.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___339_2210.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___339_2210.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___339_2210.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___339_2210.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___339_2210.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___339_2210.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___339_2210.FStar_TypeChecker_Env.erasable_types_tab)
                          }) ses1 se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____2201
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____2200
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____2199
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____2224 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____2224
                 then
                   let uu____2229 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___343_2233 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___343_2233.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___343_2233.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___343_2233.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___343_2233.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____2229
                 else ());
                ses2)
             else ses1  in
           let uu____2243 =
             tc_inductive env1 ses2 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____2243 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___350_2267 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___350_2267.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___350_2267.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___350_2267.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___350_2267.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____2279 =
             FStar_TypeChecker_TcEffect.dmff_cps_and_elaborate env ne  in
           (match uu____2279 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___364_2318 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___364_2318.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___364_2318.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___364_2318.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___364_2318.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___367_2320 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___367_2320.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___367_2320.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___367_2320.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___367_2320.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses), env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 =
             let uu____2327 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env)
                in
             if uu____2327
             then
               let ne1 =
                 let uu____2331 =
                   let uu____2332 =
                     let uu____2333 =
                       FStar_TypeChecker_TcEffect.tc_eff_decl
                         (let uu___373_2336 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___373_2336.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___373_2336.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___373_2336.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___373_2336.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___373_2336.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___373_2336.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___373_2336.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___373_2336.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___373_2336.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___373_2336.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___373_2336.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___373_2336.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___373_2336.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___373_2336.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___373_2336.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___373_2336.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___373_2336.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___373_2336.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___373_2336.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___373_2336.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___373_2336.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___373_2336.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___373_2336.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___373_2336.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___373_2336.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___373_2336.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___373_2336.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___373_2336.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___373_2336.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___373_2336.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___373_2336.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___373_2336.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___373_2336.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___373_2336.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___373_2336.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___373_2336.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___373_2336.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___373_2336.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___373_2336.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___373_2336.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___373_2336.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___373_2336.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___373_2336.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___373_2336.FStar_TypeChecker_Env.erasable_types_tab)
                          }) ne
                        in
                     FStar_All.pipe_right uu____2333
                       (fun ne1  ->
                          let uu___376_2342 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___376_2342.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___376_2342.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___376_2342.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___376_2342.FStar_Syntax_Syntax.sigattrs)
                          })
                      in
                   FStar_All.pipe_right uu____2332
                     (FStar_TypeChecker_Normalize.elim_uvars env)
                    in
                 FStar_All.pipe_right uu____2331
                   FStar_Syntax_Util.eff_decl_of_new_effect
                  in
               ((let uu____2344 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____2344
                 then
                   let uu____2349 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___380_2353 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___380_2353.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___380_2353.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___380_2353.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___380_2353.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Effect decl after phase 1: %s\n"
                     uu____2349
                 else ());
                ne1)
             else ne  in
           let ne2 = FStar_TypeChecker_TcEffect.tc_eff_decl env ne1  in
           let se1 =
             let uu___385_2361 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne2);
               FStar_Syntax_Syntax.sigrng =
                 (uu___385_2361.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___385_2361.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___385_2361.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___385_2361.FStar_Syntax_Syntax.sigattrs)
             }  in
           ([se1], [], env0)
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let sub2 = FStar_TypeChecker_TcEffect.tc_lift env sub1 r  in
           let se1 =
             let uu___391_2369 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_sub_effect sub2);
               FStar_Syntax_Syntax.sigrng =
                 (uu___391_2369.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___391_2369.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___391_2369.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___391_2369.FStar_Syntax_Syntax.sigattrs)
             }  in
           ([se1], [], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let uu____2383 =
             FStar_TypeChecker_TcEffect.tc_effect_abbrev env
               (lid, uvs, tps, c) r
              in
           (match uu____2383 with
            | (lid1,uvs1,tps1,c1) ->
                let se1 =
                  let uu___406_2407 = se  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_effect_abbrev
                         (lid1, uvs1, tps1, c1, flags));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___406_2407.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___406_2407.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___406_2407.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___406_2407.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([se1], [], env0))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____2414,uu____2415,uu____2416) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_2421  ->
                   match uu___1_2421 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____2424 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____2430,uu____2431) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_2440  ->
                   match uu___1_2440 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____2443 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____2454 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____2454
             then
               let uu____2457 =
                 let uu____2463 =
                   let uu____2465 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____2465
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____2463)
                  in
               FStar_Errors.raise_error uu____2457 r
             else ());
            (let uu____2471 =
               let uu____2480 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____2480
               then
                 let uu____2491 =
                   tc_declare_typ
                     (let uu___430_2494 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___430_2494.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___430_2494.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___430_2494.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___430_2494.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___430_2494.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___430_2494.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___430_2494.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___430_2494.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___430_2494.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___430_2494.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___430_2494.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___430_2494.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___430_2494.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___430_2494.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___430_2494.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___430_2494.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___430_2494.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___430_2494.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___430_2494.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___430_2494.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___430_2494.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___430_2494.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___430_2494.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___430_2494.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___430_2494.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___430_2494.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___430_2494.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___430_2494.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___430_2494.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___430_2494.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___430_2494.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___430_2494.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___430_2494.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___430_2494.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___430_2494.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.try_solve_implicits_hook =
                          (uu___430_2494.FStar_TypeChecker_Env.try_solve_implicits_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___430_2494.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___430_2494.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___430_2494.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___430_2494.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___430_2494.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___430_2494.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___430_2494.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___430_2494.FStar_TypeChecker_Env.strict_args_tab);
                        FStar_TypeChecker_Env.erasable_types_tab =
                          (uu___430_2494.FStar_TypeChecker_Env.erasable_types_tab)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____2491 with
                 | (uvs1,t1) ->
                     ((let uu____2519 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____2519
                       then
                         let uu____2524 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____2526 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____2524 uu____2526
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____2471 with
             | (uvs1,t1) ->
                 let uu____2561 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____2561 with
                  | (uvs2,t2) ->
                      ([(let uu___443_2591 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___443_2591.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___443_2591.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___443_2591.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___443_2591.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____2596 =
             let uu____2605 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____2605
             then
               let uu____2616 =
                 tc_assume
                   (let uu___452_2619 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___452_2619.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___452_2619.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___452_2619.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___452_2619.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___452_2619.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___452_2619.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___452_2619.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___452_2619.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___452_2619.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___452_2619.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___452_2619.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___452_2619.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___452_2619.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___452_2619.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___452_2619.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___452_2619.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___452_2619.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___452_2619.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___452_2619.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___452_2619.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___452_2619.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___452_2619.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___452_2619.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___452_2619.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___452_2619.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___452_2619.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___452_2619.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___452_2619.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___452_2619.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___452_2619.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___452_2619.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___452_2619.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___452_2619.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___452_2619.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___452_2619.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___452_2619.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___452_2619.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___452_2619.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___452_2619.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___452_2619.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___452_2619.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___452_2619.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___452_2619.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___452_2619.FStar_TypeChecker_Env.erasable_types_tab)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____2616 with
               | (uvs1,t1) ->
                   ((let uu____2645 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____2645
                     then
                       let uu____2650 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____2652 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____2650
                         uu____2652
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____2596 with
            | (uvs1,t1) ->
                let uu____2687 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____2687 with
                 | (uvs2,t2) ->
                     ([(let uu___465_2717 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___465_2717.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___465_2717.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___465_2717.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___465_2717.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____2721 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____2721 with
            | (e1,c,g1) ->
                let uu____2741 =
                  let uu____2748 = FStar_TypeChecker_Common.lcomp_comp c  in
                  match uu____2748 with
                  | (c1,g_lc) ->
                      let uu____2761 =
                        let uu____2768 =
                          let uu____2771 =
                            FStar_Syntax_Util.ml_comp
                              FStar_Syntax_Syntax.t_unit r
                             in
                          FStar_Pervasives_Native.Some uu____2771  in
                        FStar_TypeChecker_TcTerm.check_expected_effect env2
                          uu____2768 (e1, c1)
                         in
                      (match uu____2761 with
                       | (e2,_x,g) ->
                           let uu____2781 =
                             FStar_TypeChecker_Env.conj_guard g_lc g  in
                           (e2, _x, uu____2781))
                   in
                (match uu____2741 with
                 | (e2,uu____2793,g) ->
                     ((let uu____2796 = FStar_TypeChecker_Env.conj_guard g1 g
                          in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____2796);
                      (let se1 =
                         let uu___487_2798 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___487_2798.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___487_2798.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___487_2798.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___487_2798.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____2810 = FStar_Options.debug_any ()  in
             if uu____2810
             then
               let uu____2813 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____2815 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____2813
                 uu____2815
             else ());
            (let uu____2820 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____2820 with
             | (t1,uu____2838,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____2852 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____2852 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____2855 =
                              let uu____2861 =
                                let uu____2863 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____2865 =
                                  let uu____2867 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____2867
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____2863 uu____2865
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____2861)
                               in
                            FStar_Errors.raise_error uu____2855 r
                        | uu____2879 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___508_2884 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___508_2884.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___508_2884.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___508_2884.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___508_2884.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___508_2884.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___508_2884.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___508_2884.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___508_2884.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___508_2884.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___508_2884.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___508_2884.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___508_2884.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___508_2884.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___508_2884.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___508_2884.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___508_2884.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___508_2884.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___508_2884.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___508_2884.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___508_2884.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___508_2884.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___508_2884.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___508_2884.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___508_2884.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___508_2884.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___508_2884.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___508_2884.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___508_2884.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___508_2884.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___508_2884.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___508_2884.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___508_2884.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___508_2884.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___508_2884.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___508_2884.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___508_2884.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.try_solve_implicits_hook =
                          (uu___508_2884.FStar_TypeChecker_Env.try_solve_implicits_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___508_2884.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___508_2884.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___508_2884.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___508_2884.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___508_2884.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___508_2884.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___508_2884.FStar_TypeChecker_Env.strict_args_tab);
                        FStar_TypeChecker_Env.erasable_types_tab =
                          (uu___508_2884.FStar_TypeChecker_Env.erasable_types_tab)
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
                 let uu____2952 =
                   let uu____2954 =
                     let uu____2963 = drop_logic val_q  in
                     let uu____2966 = drop_logic q'  in
                     (uu____2963, uu____2966)  in
                   match uu____2954 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____2952
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____2993 =
                      let uu____2999 =
                        let uu____3001 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____3003 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____3005 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____3001 uu____3003 uu____3005
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____2999)
                       in
                    FStar_Errors.raise_error uu____2993 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____3042 =
                   let uu____3043 = FStar_Syntax_Subst.compress def  in
                   uu____3043.FStar_Syntax_Syntax.n  in
                 match uu____3042 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____3055,uu____3056)
                     -> binders
                 | uu____3081 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____3093;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____3198) -> val_bs1
                     | (uu____3229,[]) -> val_bs1
                     | ((body_bv,uu____3261)::bt,(val_bv,aqual)::vt) ->
                         let uu____3318 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____3342) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___577_3356 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___579_3359 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___579_3359.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___577_3356.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___577_3356.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____3318
                      in
                   let uu____3366 =
                     let uu____3373 =
                       let uu____3374 =
                         let uu____3389 = rename_binders1 def_bs val_bs  in
                         (uu____3389, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____3374  in
                     FStar_Syntax_Syntax.mk uu____3373  in
                   uu____3366 FStar_Pervasives_Native.None r1
               | uu____3408 -> typ1  in
             let uu___585_3409 = lb  in
             let uu____3410 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___585_3409.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___585_3409.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____3410;
               FStar_Syntax_Syntax.lbeff =
                 (uu___585_3409.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___585_3409.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___585_3409.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___585_3409.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____3413 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____3468  ->
                     fun lb  ->
                       match uu____3468 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____3514 =
                             let uu____3526 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____3526 with
                             | FStar_Pervasives_Native.None  ->
                                 if lb.FStar_Syntax_Syntax.lbunivs <> []
                                 then (false, lb, quals_opt)
                                 else (gen1, lb, quals_opt)
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
                                   | uu____3606 ->
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
                                    (lb.FStar_Syntax_Syntax.lbunivs <> []) &&
                                      ((FStar_List.length
                                          lb.FStar_Syntax_Syntax.lbunivs)
                                         <> (FStar_List.length uvs))
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_IncoherentInlineUniverse,
                                        "Inline universes are incoherent with annotation from val declaration")
                                      r
                                  else ();
                                  (let uu____3653 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____3653, quals_opt1)))
                              in
                           (match uu____3514 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____3413 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____3757 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___2_3763  ->
                                match uu___2_3763 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____3768 -> false))
                         in
                      if uu____3757
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____3781 =
                    let uu____3788 =
                      let uu____3789 =
                        let uu____3803 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____3803)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____3789  in
                    FStar_Syntax_Syntax.mk uu____3788  in
                  uu____3781 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___628_3822 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___628_3822.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___628_3822.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___628_3822.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___628_3822.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___628_3822.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___628_3822.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___628_3822.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___628_3822.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___628_3822.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___628_3822.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___628_3822.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___628_3822.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___628_3822.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___628_3822.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___628_3822.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___628_3822.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___628_3822.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___628_3822.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___628_3822.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___628_3822.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___628_3822.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___628_3822.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___628_3822.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___628_3822.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___628_3822.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___628_3822.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___628_3822.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___628_3822.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___628_3822.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___628_3822.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___628_3822.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___628_3822.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___628_3822.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___628_3822.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___628_3822.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___628_3822.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___628_3822.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___628_3822.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___628_3822.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___628_3822.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___628_3822.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___628_3822.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___628_3822.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___628_3822.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                let e1 =
                  let uu____3825 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____3825
                  then
                    let drop_lbtyp e_lax =
                      let uu____3834 =
                        let uu____3835 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____3835.FStar_Syntax_Syntax.n  in
                      match uu____3834 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____3857 =
                              let uu____3858 = FStar_Syntax_Subst.compress e
                                 in
                              uu____3858.FStar_Syntax_Syntax.n  in
                            match uu____3857 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____3862,lb1::[]),uu____3864) ->
                                let uu____3880 =
                                  let uu____3881 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____3881.FStar_Syntax_Syntax.n  in
                                (match uu____3880 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____3886 -> false)
                            | uu____3888 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___653_3892 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___655_3907 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___655_3907.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___655_3907.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___655_3907.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___655_3907.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___655_3907.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___655_3907.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___653_3892.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___653_3892.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____3910 -> e_lax  in
                    let uu____3911 =
                      FStar_Util.record_time
                        (fun uu____3919  ->
                           let uu____3920 =
                             let uu____3921 =
                               let uu____3922 =
                                 FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                   (let uu___659_3931 = env'  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___659_3931.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___659_3931.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___659_3931.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___659_3931.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___659_3931.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___659_3931.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___659_3931.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___659_3931.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___659_3931.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___659_3931.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___659_3931.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___659_3931.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___659_3931.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___659_3931.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___659_3931.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___659_3931.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___659_3931.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___659_3931.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___659_3931.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___659_3931.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___659_3931.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___659_3931.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___659_3931.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___659_3931.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___659_3931.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___659_3931.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___659_3931.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___659_3931.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___659_3931.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___659_3931.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___659_3931.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___659_3931.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___659_3931.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___659_3931.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___659_3931.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___659_3931.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___659_3931.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___659_3931.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___659_3931.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___659_3931.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___659_3931.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___659_3931.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___659_3931.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___659_3931.FStar_TypeChecker_Env.erasable_types_tab)
                                    }) e
                                  in
                               FStar_All.pipe_right uu____3922
                                 (fun uu____3944  ->
                                    match uu____3944 with
                                    | (e1,uu____3952,uu____3953) -> e1)
                                in
                             FStar_All.pipe_right uu____3921
                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                  env')
                              in
                           FStar_All.pipe_right uu____3920 drop_lbtyp)
                       in
                    match uu____3911 with
                    | (e1,ms) ->
                        ((let uu____3959 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TwoPhases")
                             in
                          if uu____3959
                          then
                            let uu____3964 =
                              FStar_Syntax_Print.term_to_string e1  in
                            FStar_Util.print1
                              "Let binding after phase 1: %s\n" uu____3964
                          else ());
                         (let uu____3970 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TCDeclTime")
                             in
                          if uu____3970
                          then
                            let uu____3975 = FStar_Util.string_of_int ms  in
                            FStar_Util.print1
                              "Let binding elaborated (phase 1) in %s milliseconds\n"
                              uu____3975
                          else ());
                         e1)
                  else e  in
                let uu____3982 =
                  let uu____3991 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____3991 with
                  | FStar_Pervasives_Native.None  ->
                      ((se.FStar_Syntax_Syntax.sigattrs),
                        FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some
                      (ats,(tau,FStar_Pervasives_Native.None )::[]) ->
                      (ats, (FStar_Pervasives_Native.Some tau))
                  | FStar_Pervasives_Native.Some (ats,args) ->
                      (FStar_Errors.log_issue r
                         (FStar_Errors.Warning_UnrecognizedAttribute,
                           "Ill-formed application of `postprocess_with`");
                       ((se.FStar_Syntax_Syntax.sigattrs),
                         FStar_Pervasives_Native.None))
                   in
                (match uu____3982 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___689_4096 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___689_4096.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___689_4096.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___689_4096.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___689_4096.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___696_4109 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___696_4109.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___696_4109.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___696_4109.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___696_4109.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___696_4109.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___696_4109.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____4110 =
                       FStar_Util.record_time
                         (fun uu____4129  ->
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              env' e1)
                        in
                     (match uu____4110 with
                      | (r1,ms) ->
                          ((let uu____4157 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TCDeclTime")
                               in
                            if uu____4157
                            then
                              let uu____4162 = FStar_Util.string_of_int ms
                                 in
                              FStar_Util.print1
                                "Let binding typechecked in phase 2 in %s milliseconds\n"
                                uu____4162
                            else ());
                           (let uu____4167 =
                              match r1 with
                              | ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                                   FStar_Syntax_Syntax.pos = uu____4192;
                                   FStar_Syntax_Syntax.vars = uu____4193;_},uu____4194,g)
                                  when FStar_TypeChecker_Env.is_trivial g ->
                                  let lbs2 =
                                    let uu____4224 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.snd lbs1)
                                        (FStar_List.map rename_parameters)
                                       in
                                    ((FStar_Pervasives_Native.fst lbs1),
                                      uu____4224)
                                     in
                                  let lbs3 =
                                    let uu____4248 =
                                      match post_tau with
                                      | FStar_Pervasives_Native.Some tau ->
                                          FStar_List.map (postprocess_lb tau)
                                            (FStar_Pervasives_Native.snd lbs2)
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.snd lbs2
                                       in
                                    ((FStar_Pervasives_Native.fst lbs2),
                                      uu____4248)
                                     in
                                  let quals1 =
                                    match e2.FStar_Syntax_Syntax.n with
                                    | FStar_Syntax_Syntax.Tm_meta
                                        (uu____4271,FStar_Syntax_Syntax.Meta_desugared
                                         (FStar_Syntax_Syntax.Masked_effect
                                         ))
                                        ->
                                        FStar_Syntax_Syntax.HasMaskedEffect
                                        :: quals
                                    | uu____4276 -> quals  in
                                  ((let uu___726_4285 = se1  in
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_let
                                           (lbs3, lids));
                                      FStar_Syntax_Syntax.sigrng =
                                        (uu___726_4285.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals = quals1;
                                      FStar_Syntax_Syntax.sigmeta =
                                        (uu___726_4285.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (uu___726_4285.FStar_Syntax_Syntax.sigattrs)
                                    }), lbs3)
                              | uu____4288 ->
                                  failwith
                                    "impossible (typechecking should preserve Tm_let)"
                               in
                            match uu____4167 with
                            | (se2,lbs1) ->
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
                                 (let uu____4344 = log env1  in
                                  if uu____4344
                                  then
                                    let uu____4347 =
                                      let uu____4349 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.snd lbs1)
                                          (FStar_List.map
                                             (fun lb  ->
                                                let should_log =
                                                  let uu____4369 =
                                                    let uu____4378 =
                                                      let uu____4379 =
                                                        let uu____4382 =
                                                          FStar_Util.right
                                                            lb.FStar_Syntax_Syntax.lbname
                                                           in
                                                        uu____4382.FStar_Syntax_Syntax.fv_name
                                                         in
                                                      uu____4379.FStar_Syntax_Syntax.v
                                                       in
                                                    FStar_TypeChecker_Env.try_lookup_val_decl
                                                      env1 uu____4378
                                                     in
                                                  match uu____4369 with
                                                  | FStar_Pervasives_Native.None
                                                       -> true
                                                  | uu____4391 -> false  in
                                                if should_log
                                                then
                                                  let uu____4403 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  let uu____4405 =
                                                    FStar_Syntax_Print.term_to_string
                                                      lb.FStar_Syntax_Syntax.lbtyp
                                                     in
                                                  FStar_Util.format2
                                                    "let %s : %s" uu____4403
                                                    uu____4405
                                                else ""))
                                         in
                                      FStar_All.pipe_right uu____4349
                                        (FStar_String.concat "\n")
                                       in
                                    FStar_Util.print1 "%s\n" uu____4347
                                  else ());
                                 check_must_erase_attribute env0 se2;
                                 ([se2], [], env0))))))))
  
let (tc_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun se  ->
      let env1 = set_hint_correlator env se  in
      (let uu____4457 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____4457
       then
         let uu____4460 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____4460
       else ());
      (let uu____4465 = get_fail_se se  in
       match uu____4465 with
       | FStar_Pervasives_Native.Some (uu____4486,false ) when
           let uu____4503 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____4503 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___757_4529 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___757_4529.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___757_4529.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___757_4529.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___757_4529.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___757_4529.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___757_4529.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___757_4529.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___757_4529.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___757_4529.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___757_4529.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___757_4529.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___757_4529.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___757_4529.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___757_4529.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___757_4529.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___757_4529.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___757_4529.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___757_4529.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___757_4529.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___757_4529.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___757_4529.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___757_4529.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___757_4529.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___757_4529.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___757_4529.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___757_4529.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___757_4529.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___757_4529.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___757_4529.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___757_4529.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___757_4529.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___757_4529.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___757_4529.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___757_4529.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___757_4529.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.try_solve_implicits_hook =
                   (uu___757_4529.FStar_TypeChecker_Env.try_solve_implicits_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___757_4529.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___757_4529.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___757_4529.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___757_4529.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___757_4529.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___757_4529.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___757_4529.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___757_4529.FStar_TypeChecker_Env.strict_args_tab);
                 FStar_TypeChecker_Env.erasable_types_tab =
                   (uu___757_4529.FStar_TypeChecker_Env.erasable_types_tab)
               }
             else env1  in
           ((let uu____4534 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____4534
             then
               let uu____4537 =
                 let uu____4539 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____4539
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____4537
             else ());
            (let uu____4553 =
               FStar_Errors.catch_errors
                 (fun uu____4583  ->
                    FStar_Options.with_saved_options
                      (fun uu____4595  -> tc_decl' env' se))
                in
             match uu____4553 with
             | (errs,uu____4607) ->
                 ((let uu____4637 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____4637
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____4672 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____4672  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____4684 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____4695 =
                            let uu____4705 = check_multi_eq errnos1 actual
                               in
                            match uu____4705 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- Prims.int_one), (~- Prims.int_one),
                                  (~- Prims.int_one))
                             in
                          (match uu____4695 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____4770 =
                                   let uu____4776 =
                                     let uu____4778 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____4781 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____4784 =
                                       FStar_Util.string_of_int e  in
                                     let uu____4786 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____4788 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____4778 uu____4781 uu____4784
                                       uu____4786 uu____4788
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____4776)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____4770)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____4815 .
    'Auu____4815 ->
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
               (fun uu___3_4858  ->
                  match uu___3_4858 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____4861 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____4872) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____4880 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____4890 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____4895 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____4911 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____4937 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4963) ->
            let uu____4972 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____4972
            then
              let for_export_bundle se1 uu____5009 =
                match uu____5009 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____5048,uu____5049) ->
                         let dec =
                           let uu___833_5059 = se1  in
                           let uu____5060 =
                             let uu____5061 =
                               let uu____5068 =
                                 let uu____5069 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____5069  in
                               (l, us, uu____5068)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____5061
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____5060;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___833_5059.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___833_5059.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___833_5059.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____5079,uu____5080,uu____5081) ->
                         let dec =
                           let uu___844_5089 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___844_5089.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___844_5089.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___844_5089.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____5094 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume (uu____5117,uu____5118,uu____5119)
            ->
            let uu____5120 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____5120 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____5144 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____5144
            then
              ([(let uu___860_5163 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___860_5163.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___860_5163.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___860_5163.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____5166 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_5172  ->
                         match uu___4_5172 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____5175 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____5181 ->
                             true
                         | uu____5183 -> false))
                  in
               if uu____5166 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____5204 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____5209 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5214 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____5219 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____5224 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____5242) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____5256 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____5256
            then ([], hidden)
            else
              (let dec =
                 let uu____5277 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____5277;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____5288 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____5288
            then
              let uu____5299 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___897_5313 = se  in
                        let uu____5314 =
                          let uu____5315 =
                            let uu____5322 =
                              let uu____5323 =
                                let uu____5326 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____5326.FStar_Syntax_Syntax.fv_name  in
                              uu____5323.FStar_Syntax_Syntax.v  in
                            (uu____5322, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____5315  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____5314;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___897_5313.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___897_5313.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___897_5313.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____5299, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> Prims.bool -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      fun from_cache  ->
        (let uu____5356 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____5356
         then
           let uu____5359 = FStar_Syntax_Print.sigelt_to_string se  in
           let uu____5361 = FStar_Util.string_of_bool from_cache  in
           FStar_Util.print2
             ">>>>>>>>>>>>>>Adding top-level decl to environment: %s (from_cache:%s)\n"
             uu____5359 uu____5361
         else ());
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____5366 ->
             let uu____5383 =
               let uu____5389 =
                 let uu____5391 = FStar_Syntax_Print.sigelt_to_string se  in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____5391
                  in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____5389)  in
             FStar_Errors.raise_error uu____5383
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_datacon uu____5395 ->
             let uu____5411 =
               let uu____5417 =
                 let uu____5419 = FStar_Syntax_Print.sigelt_to_string se  in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____5419
                  in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____5417)  in
             FStar_Errors.raise_error uu____5411
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_declare_typ
             (uu____5423,uu____5424,uu____5425) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___5_5430  ->
                     match uu___5_5430 with
                     | FStar_Syntax_Syntax.OnlyName  -> true
                     | uu____5433 -> false))
             -> env
         | FStar_Syntax_Syntax.Sig_let (uu____5435,uu____5436) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___5_5445  ->
                     match uu___5_5445 with
                     | FStar_Syntax_Syntax.OnlyName  -> true
                     | uu____5448 -> false))
             -> env
         | uu____5450 ->
             let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PushOptions uu____5452) ->
                  if from_cache
                  then env1
                  else
                    (let uu___934_5459 = env1  in
                     let uu____5460 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___934_5459.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___934_5459.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___934_5459.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___934_5459.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___934_5459.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___934_5459.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___934_5459.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___934_5459.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___934_5459.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___934_5459.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___934_5459.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___934_5459.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___934_5459.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___934_5459.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___934_5459.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___934_5459.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___934_5459.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___934_5459.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___934_5459.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___934_5459.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___934_5459.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___934_5459.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___934_5459.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___934_5459.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___934_5459.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___934_5459.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___934_5459.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___934_5459.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___934_5459.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___934_5459.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___934_5459.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___934_5459.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___934_5459.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___934_5459.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5460;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___934_5459.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___934_5459.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___934_5459.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___934_5459.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___934_5459.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___934_5459.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___934_5459.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___934_5459.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___934_5459.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___934_5459.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___934_5459.FStar_TypeChecker_Env.erasable_types_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PopOptions ) ->
                  if from_cache
                  then env1
                  else
                    (let uu___934_5464 = env1  in
                     let uu____5465 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___934_5464.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___934_5464.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___934_5464.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___934_5464.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___934_5464.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___934_5464.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___934_5464.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___934_5464.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___934_5464.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___934_5464.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___934_5464.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___934_5464.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___934_5464.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___934_5464.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___934_5464.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___934_5464.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___934_5464.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___934_5464.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___934_5464.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___934_5464.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___934_5464.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___934_5464.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___934_5464.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___934_5464.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___934_5464.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___934_5464.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___934_5464.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___934_5464.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___934_5464.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___934_5464.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___934_5464.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___934_5464.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___934_5464.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___934_5464.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5465;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___934_5464.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___934_5464.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___934_5464.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___934_5464.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___934_5464.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___934_5464.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___934_5464.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___934_5464.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___934_5464.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___934_5464.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___934_5464.FStar_TypeChecker_Env.erasable_types_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.SetOptions uu____5466) ->
                  if from_cache
                  then env1
                  else
                    (let uu___934_5471 = env1  in
                     let uu____5472 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___934_5471.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___934_5471.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___934_5471.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___934_5471.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___934_5471.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___934_5471.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___934_5471.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___934_5471.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___934_5471.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___934_5471.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___934_5471.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___934_5471.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___934_5471.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___934_5471.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___934_5471.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___934_5471.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___934_5471.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___934_5471.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___934_5471.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___934_5471.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___934_5471.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___934_5471.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___934_5471.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___934_5471.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___934_5471.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___934_5471.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___934_5471.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___934_5471.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___934_5471.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___934_5471.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___934_5471.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___934_5471.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___934_5471.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___934_5471.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5472;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___934_5471.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___934_5471.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___934_5471.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___934_5471.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___934_5471.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___934_5471.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___934_5471.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___934_5471.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___934_5471.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___934_5471.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___934_5471.FStar_TypeChecker_Env.erasable_types_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.ResetOptions uu____5473) ->
                  if from_cache
                  then env1
                  else
                    (let uu___934_5480 = env1  in
                     let uu____5481 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___934_5480.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___934_5480.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___934_5480.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___934_5480.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___934_5480.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___934_5480.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___934_5480.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___934_5480.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___934_5480.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___934_5480.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___934_5480.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___934_5480.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___934_5480.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___934_5480.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___934_5480.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___934_5480.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___934_5480.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___934_5480.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___934_5480.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___934_5480.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___934_5480.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___934_5480.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___934_5480.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___934_5480.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___934_5480.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___934_5480.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___934_5480.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___934_5480.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___934_5480.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___934_5480.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___934_5480.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___934_5480.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___934_5480.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___934_5480.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5481;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___934_5480.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___934_5480.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___934_5480.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___934_5480.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___934_5480.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___934_5480.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___934_5480.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___934_5480.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___934_5480.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___934_5480.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___934_5480.FStar_TypeChecker_Env.erasable_types_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.RestartSolver ) ->
                  if from_cache
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
                            let uu____5497 =
                              FStar_Syntax_Util.action_as_lb
                                ne.FStar_Syntax_Syntax.mname a
                                (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Env.push_sigelt env3 uu____5497)
                       env2)
              | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
                  let sub_or_lift_t =
                    let uu____5506 =
                      (FStar_TypeChecker_Env.is_layered_effect env1
                         sub1.FStar_Syntax_Syntax.source)
                        ||
                        (FStar_TypeChecker_Env.is_layered_effect env1
                           sub1.FStar_Syntax_Syntax.target)
                       in
                    if uu____5506
                    then
                      let uu____5515 =
                        let uu____5520 =
                          FStar_All.pipe_right
                            sub1.FStar_Syntax_Syntax.lift_wp FStar_Util.must
                           in
                        FStar_TypeChecker_Util.lift_tf_layered_effect
                          sub1.FStar_Syntax_Syntax.target uu____5520
                         in
                      FStar_Util.Inr uu____5515
                    else FStar_Util.Inl sub1  in
                  FStar_TypeChecker_Env.update_effect_lattice env1
                    sub1.FStar_Syntax_Syntax.source
                    sub1.FStar_Syntax_Syntax.target sub_or_lift_t
              | uu____5529 -> env1))
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____5598 se =
        match uu____5598 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____5651 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____5651
              then
                let uu____5654 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____5654
              else ());
             (let uu____5659 = tc_decl env1 se  in
              match uu____5659 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____5712 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____5712
                             then
                               let uu____5716 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____5716
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____5732 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____5732
                             then
                               let uu____5736 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____5736
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
                    (let uu____5754 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____5754
                     then
                       let uu____5759 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____5768 =
                                  let uu____5770 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____5770 "\n"  in
                                Prims.op_Hat s uu____5768) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____5759
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____5780 =
                       let uu____5789 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____5789
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____5831 se1 =
                            match uu____5831 with
                            | (exports1,hidden1) ->
                                let uu____5859 = for_export env3 hidden1 se1
                                   in
                                (match uu____5859 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____5780 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____6013 = acc  in
        match uu____6013 with
        | (uu____6048,uu____6049,env1,uu____6051) ->
            let r =
              let uu____6085 =
                let uu____6089 =
                  let uu____6091 = FStar_TypeChecker_Env.current_module env1
                     in
                  FStar_Ident.string_of_lid uu____6091  in
                FStar_Pervasives_Native.Some uu____6089  in
              FStar_Profiling.profile
                (fun uu____6114  -> process_one_decl acc se) uu____6085
                "FStar.TypeChecker.Tc.process_one_decl"
               in
            ((let uu____6117 = FStar_Options.profile_group_by_decls ()  in
              if uu____6117
              then
                let tag =
                  match FStar_Syntax_Util.lids_of_sigelt se with
                  | hd1::uu____6124 -> FStar_Ident.string_of_lid hd1
                  | uu____6127 ->
                      FStar_Range.string_of_range
                        (FStar_Syntax_Util.range_of_sigelt se)
                   in
                FStar_Profiling.report_and_clear tag
              else ());
             r)
         in
      let uu____6132 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____6132 with
      | (ses1,exports,env1,uu____6180) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
  
let (check_exports :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> unit)
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env1 =
          let uu___1022_6218 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1022_6218.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1022_6218.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1022_6218.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1022_6218.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1022_6218.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1022_6218.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1022_6218.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1022_6218.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1022_6218.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1022_6218.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___1022_6218.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1022_6218.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1022_6218.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1022_6218.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1022_6218.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___1022_6218.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1022_6218.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___1022_6218.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1022_6218.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___1022_6218.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1022_6218.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1022_6218.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1022_6218.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1022_6218.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1022_6218.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1022_6218.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1022_6218.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1022_6218.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1022_6218.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1022_6218.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1022_6218.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1022_6218.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1022_6218.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1022_6218.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1022_6218.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___1022_6218.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___1022_6218.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1022_6218.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1022_6218.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1022_6218.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1022_6218.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1022_6218.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1022_6218.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        let check_term lid univs1 t =
          let uu____6238 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____6238 with
          | (univs2,t1) ->
              ((let uu____6246 =
                  let uu____6248 =
                    let uu____6254 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____6254  in
                  FStar_All.pipe_left uu____6248
                    (FStar_Options.Other "Exports")
                   in
                if uu____6246
                then
                  let uu____6258 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____6260 =
                    let uu____6262 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____6262
                      (FStar_String.concat ", ")
                     in
                  let uu____6279 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____6258 uu____6260 uu____6279
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____6285 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____6285 (fun a1  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____6311 =
             let uu____6313 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____6315 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____6313 uu____6315
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____6311);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6326) ->
              let uu____6335 =
                let uu____6337 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6337  in
              if uu____6335
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____6351,uu____6352) ->
              let t =
                let uu____6364 =
                  let uu____6371 =
                    let uu____6372 =
                      let uu____6387 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____6387)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____6372  in
                  FStar_Syntax_Syntax.mk uu____6371  in
                uu____6364 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____6403,uu____6404,uu____6405) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____6415 =
                let uu____6417 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6417  in
              if uu____6415 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____6425,lbs),uu____6427) ->
              let uu____6438 =
                let uu____6440 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6440  in
              if uu____6438
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
              (l,univs1,binders,comp,flags) ->
              let uu____6463 =
                let uu____6465 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6465  in
              if uu____6463
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____6486 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____6487 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____6494 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____6495 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____6496 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____6497 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____6504 -> ()  in
        let uu____6505 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____6505 then () else FStar_List.iter check_sigelt exports
  
let (extract_interface :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul)
  =
  fun en  ->
    fun m  ->
      let is_abstract = FStar_List.contains FStar_Syntax_Syntax.Abstract  in
      let is_irreducible1 =
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
             | FStar_Syntax_Syntax.Projector (l,uu____6611) -> true
             | uu____6613 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____6643 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____6682 ->
                   let uu____6683 =
                     let uu____6690 =
                       let uu____6691 =
                         let uu____6706 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____6706)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____6691  in
                     FStar_Syntax_Syntax.mk uu____6690  in
                   uu____6683 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____6723,uu____6724) ->
            let s1 =
              let uu___1148_6734 = s  in
              let uu____6735 =
                let uu____6736 =
                  let uu____6743 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____6743)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____6736  in
              let uu____6744 =
                let uu____6747 =
                  let uu____6750 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____6750  in
                FStar_Syntax_Syntax.Assumption :: uu____6747  in
              {
                FStar_Syntax_Syntax.sigel = uu____6735;
                FStar_Syntax_Syntax.sigrng =
                  (uu___1148_6734.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____6744;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___1148_6734.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___1148_6734.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____6753 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____6778 lbdef =
        match uu____6778 with
        | (uvs,t) ->
            let attrs =
              let uu____6789 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____6789
              then
                let uu____6794 =
                  let uu____6795 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____6795
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____6794 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___1161_6798 = s  in
            let uu____6799 =
              let uu____6802 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____6802  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___1161_6798.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____6799;
              FStar_Syntax_Syntax.sigmeta =
                (uu___1161_6798.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____6820 -> failwith "Impossible!"  in
        let c_opt =
          let uu____6827 = FStar_Syntax_Util.is_unit t  in
          if uu____6827
          then
            let uu____6834 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____6834
          else
            (let uu____6841 =
               let uu____6842 = FStar_Syntax_Subst.compress t  in
               uu____6842.FStar_Syntax_Syntax.n  in
             match uu____6841 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____6849,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____6873 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____6885 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____6885
            then false
            else
              (let uu____6892 = FStar_Syntax_Util.is_pure_or_ghost_comp c  in
               if uu____6892
               then true
               else
                 (let uu____6899 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____6899))
         in
      let extract_sigelt s =
        (let uu____6911 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____6911
         then
           let uu____6914 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____6914
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____6921 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____6941 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____6960 ->
             failwith
               "Impossible! extract_interface: trying to extract splice"
         | FStar_Syntax_Syntax.Sig_bundle (sigelts,lidents1) ->
             if is_abstract s.FStar_Syntax_Syntax.sigquals
             then
               FStar_All.pipe_right sigelts
                 (FStar_List.fold_left
                    (fun sigelts1  ->
                       fun s1  ->
                         match s1.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_inductive_typ
                             (lid,uu____7006,uu____7007,uu____7008,uu____7009,uu____7010)
                             ->
                             ((let uu____7020 =
                                 let uu____7023 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____7023  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____7020);
                              (let uu____7072 = vals_of_abstract_inductive s1
                                  in
                               FStar_List.append uu____7072 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____7076,uu____7077,uu____7078,uu____7079,uu____7080)
                             ->
                             ((let uu____7088 =
                                 let uu____7091 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____7091  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____7088);
                              sigelts1)
                         | uu____7140 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____7149 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____7149
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____7159 =
                    let uu___1225_7160 = s  in
                    let uu____7161 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1225_7160.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1225_7160.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____7161;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1225_7160.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1225_7160.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____7159])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____7172 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____7172
             then []
             else
               (let uu____7179 = lbs  in
                match uu____7179 with
                | (flbs,slbs) ->
                    let typs_and_defs =
                      FStar_All.pipe_right slbs
                        (FStar_List.map
                           (fun lb  ->
                              ((lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp),
                                (lb.FStar_Syntax_Syntax.lbdef))))
                       in
                    let is_lemma1 =
                      FStar_List.existsML
                        (fun uu____7241  ->
                           match uu____7241 with
                           | (uu____7249,t,uu____7251) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____7268  ->
                             match uu____7268 with
                             | (u,t,d) -> val_of_lb s lid (u, t) d) lids
                        typs_and_defs
                       in
                    if
                      ((is_abstract s.FStar_Syntax_Syntax.sigquals) ||
                         (is_irreducible1 s.FStar_Syntax_Syntax.sigquals))
                        || is_lemma1
                    then vals
                    else
                      (let should_keep_defs =
                         FStar_List.existsML
                           (fun uu____7295  ->
                              match uu____7295 with
                              | (uu____7303,t,uu____7305) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____7317,uu____7318) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____7326 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____7355 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____7355) uu____7326
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____7359 =
                    let uu___1267_7360 = s  in
                    let uu____7361 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1267_7360.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1267_7360.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____7361;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1267_7360.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1267_7360.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____7359]
                else [])
             else
               (let uu____7368 =
                  let uu___1269_7369 = s  in
                  let uu____7370 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1269_7369.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1269_7369.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____7370;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1269_7369.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1269_7369.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____7368])
         | FStar_Syntax_Syntax.Sig_new_effect uu____7373 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7374 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____7375 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7376 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____7389 -> [s])
         in
      let uu___1281_7390 = m  in
      let uu____7391 =
        let uu____7392 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____7392 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___1281_7390.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____7391;
        FStar_Syntax_Syntax.exports =
          (uu___1281_7390.FStar_Syntax_Syntax.exports);
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
        (fun uu____7443  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____7490  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____7505 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____7505
  
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
        FStar_Options.should_verify
          (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      let action = if verify then "Verifying" else "Lax-checking"  in
      let label1 =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation"  in
      (let uu____7594 = FStar_Options.debug_any ()  in
       if uu____7594
       then
         FStar_Util.print3 "%s %s of %s\n" action label1
           (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
       else ());
      (let name =
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
          in
       let env1 =
         let uu___1306_7610 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___1306_7610.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___1306_7610.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___1306_7610.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___1306_7610.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___1306_7610.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___1306_7610.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___1306_7610.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___1306_7610.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___1306_7610.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___1306_7610.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___1306_7610.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___1306_7610.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___1306_7610.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___1306_7610.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___1306_7610.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___1306_7610.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___1306_7610.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___1306_7610.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___1306_7610.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___1306_7610.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___1306_7610.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___1306_7610.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___1306_7610.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___1306_7610.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___1306_7610.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___1306_7610.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___1306_7610.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___1306_7610.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___1306_7610.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___1306_7610.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___1306_7610.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___1306_7610.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___1306_7610.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___1306_7610.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___1306_7610.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___1306_7610.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___1306_7610.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___1306_7610.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___1306_7610.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___1306_7610.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___1306_7610.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___1306_7610.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___1306_7610.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___1306_7610.FStar_TypeChecker_Env.erasable_types_tab)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____7612 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____7612 with
       | (ses,exports,env3) ->
           ((let uu___1314_7645 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___1314_7645.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___1314_7645.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___1314_7645.FStar_Syntax_Syntax.is_interface)
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
        let uu____7674 = tc_decls env decls  in
        match uu____7674 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___1323_7705 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___1323_7705.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___1323_7705.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___1323_7705.FStar_Syntax_Syntax.is_interface)
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
          Prims.op_Hat "Internals for "
            (m.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        let env01 = push_context env0 msg  in
        let uu____7766 = tc_partial_modul env01 m  in
        match uu____7766 with
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
                (let uu____7803 = FStar_Errors.get_err_count ()  in
                 uu____7803 = Prims.int_zero)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____7814 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____7814
                then
                  let uu____7818 =
                    let uu____7820 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____7820 then "" else " (in lax mode) "  in
                  let uu____7828 =
                    let uu____7830 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____7830
                    then
                      let uu____7834 =
                        let uu____7836 = FStar_Syntax_Print.modul_to_string m
                           in
                        Prims.op_Hat uu____7836 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____7834
                    else ""  in
                  let uu____7843 =
                    let uu____7845 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____7845
                    then
                      let uu____7849 =
                        let uu____7851 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____7851 "\n"  in
                      Prims.op_Hat "\nto: " uu____7849
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____7818
                    uu____7828 uu____7843
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___1349_7865 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1349_7865.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1349_7865.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1349_7865.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1349_7865.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1349_7865.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1349_7865.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1349_7865.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1349_7865.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1349_7865.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1349_7865.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1349_7865.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1349_7865.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1349_7865.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1349_7865.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1349_7865.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1349_7865.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1349_7865.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1349_7865.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1349_7865.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1349_7865.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1349_7865.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1349_7865.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1349_7865.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1349_7865.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1349_7865.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1349_7865.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1349_7865.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1349_7865.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1349_7865.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1349_7865.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1349_7865.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1349_7865.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1349_7865.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1349_7865.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1349_7865.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1349_7865.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1349_7865.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1349_7865.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1349_7865.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1349_7865.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1349_7865.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1349_7865.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1349_7865.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1349_7865.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___1349_7865.FStar_TypeChecker_Env.erasable_types_tab)
                    }  in
                  let en02 =
                    let uu___1352_7867 = en01  in
                    let uu____7868 =
                      let uu____7883 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____7883, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1352_7867.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1352_7867.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1352_7867.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1352_7867.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1352_7867.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1352_7867.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1352_7867.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1352_7867.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1352_7867.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1352_7867.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1352_7867.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1352_7867.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1352_7867.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1352_7867.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1352_7867.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1352_7867.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1352_7867.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1352_7867.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1352_7867.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1352_7867.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1352_7867.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1352_7867.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1352_7867.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1352_7867.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1352_7867.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1352_7867.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1352_7867.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1352_7867.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1352_7867.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1352_7867.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1352_7867.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____7868;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1352_7867.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1352_7867.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1352_7867.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1352_7867.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1352_7867.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1352_7867.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1352_7867.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1352_7867.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1352_7867.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1352_7867.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1352_7867.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1352_7867.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1352_7867.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___1352_7867.FStar_TypeChecker_Env.erasable_types_tab)
                    }  in
                  let uu____7929 =
                    let uu____7931 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____7931  in
                  if uu____7929
                  then
                    ((let uu____7935 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____7935 (fun a2  -> ()));
                     en02)
                  else en02  in
                let uu____7939 = tc_modul en0 modul_iface true  in
                match uu____7939 with
                | (modul_iface1,env) ->
                    ((let uu___1361_7952 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___1361_7952.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___1361_7952.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___1361_7952.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___1363_7956 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___1363_7956.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___1363_7956.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___1363_7956.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____7959 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____7959 FStar_Util.smap_clear);
               (let uu____7995 =
                  ((let uu____7999 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____7999) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____8002 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____8002)
                   in
                if uu____7995 then check_exports env modul exports else ());
               (let uu____8008 =
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____8008 (fun a3  -> ()));
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
        let uu____8023 =
          let uu____8025 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____8025  in
        push_context env uu____8023  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = add_sigelt_to_env env2 se true  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____8047 =
                         FStar_TypeChecker_Env.lookup_sigelt env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____8050 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____8050 with | (uu____8057,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____8082 = FStar_Options.debug_any ()  in
         if uu____8082
         then
           let uu____8085 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____8085
         else ());
        (let uu____8097 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____8097
         then
           let uu____8100 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____8100
         else ());
        (let env1 =
           let uu___1393_8106 = env  in
           let uu____8107 =
             let uu____8109 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____8109  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___1393_8106.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___1393_8106.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___1393_8106.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___1393_8106.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___1393_8106.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___1393_8106.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___1393_8106.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___1393_8106.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___1393_8106.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___1393_8106.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___1393_8106.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___1393_8106.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___1393_8106.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___1393_8106.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___1393_8106.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___1393_8106.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___1393_8106.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___1393_8106.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___1393_8106.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___1393_8106.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____8107;
             FStar_TypeChecker_Env.lax_universes =
               (uu___1393_8106.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___1393_8106.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___1393_8106.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___1393_8106.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___1393_8106.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___1393_8106.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___1393_8106.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___1393_8106.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___1393_8106.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___1393_8106.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___1393_8106.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___1393_8106.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___1393_8106.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___1393_8106.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___1393_8106.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___1393_8106.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___1393_8106.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___1393_8106.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___1393_8106.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___1393_8106.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___1393_8106.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___1393_8106.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___1393_8106.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___1393_8106.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___1393_8106.FStar_TypeChecker_Env.erasable_types_tab)
           }  in
         let uu____8111 = tc_modul env1 m b  in
         match uu____8111 with
         | (m1,env2) ->
             ((let uu____8123 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____8123
               then
                 let uu____8126 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____8126
               else ());
              (let uu____8132 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____8132
               then
                 let normalize_toplevel_lets se =
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_let ((b1,lbs),ids) ->
                       let n1 =
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
                         let uu____8170 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____8170 with
                         | (univnames1,e) ->
                             let uu___1415_8177 = lb  in
                             let uu____8178 =
                               let uu____8181 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____8181 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1415_8177.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1415_8177.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1415_8177.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1415_8177.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____8178;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1415_8177.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1415_8177.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___1417_8182 = se  in
                       let uu____8183 =
                         let uu____8184 =
                           let uu____8191 =
                             let uu____8192 = FStar_List.map update lbs  in
                             (b1, uu____8192)  in
                           (uu____8191, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____8184  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____8183;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1417_8182.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1417_8182.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1417_8182.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___1417_8182.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____8200 -> se  in
                 let normalized_module =
                   let uu___1421_8202 = m1  in
                   let uu____8203 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___1421_8202.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____8203;
                     FStar_Syntax_Syntax.exports =
                       (uu___1421_8202.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___1421_8202.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____8204 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____8204
               else ());
              (m1, env2)))
  