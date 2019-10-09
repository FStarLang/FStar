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
               FStar_Syntax_Syntax.sigattrs = uu____259;
               FStar_Syntax_Syntax.sigopts = uu____260;_}::{
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               FStar_Syntax_Syntax.Sig_datacon
                                                               (lex_top1,uu____262,_t_top,_lex_t_top,_300,uu____265);
                                                             FStar_Syntax_Syntax.sigrng
                                                               = r1;
                                                             FStar_Syntax_Syntax.sigquals
                                                               = [];
                                                             FStar_Syntax_Syntax.sigmeta
                                                               = uu____267;
                                                             FStar_Syntax_Syntax.sigattrs
                                                               = uu____268;
                                                             FStar_Syntax_Syntax.sigopts
                                                               = uu____269;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____271,_t_cons,_lex_t_cons,_310,uu____274);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____276;
                 FStar_Syntax_Syntax.sigattrs = uu____277;
                 FStar_Syntax_Syntax.sigopts = uu____278;_}::[]
               when
               ((_300 = Prims.int_zero) && (_310 = Prims.int_zero)) &&
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
                   FStar_Syntax_Syntax.sigattrs = [];
                   FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                 }  in
               let utop =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r1)
                  in
               let lex_top_t =
                 let uu____337 =
                   let uu____344 =
                     let uu____345 =
                       let uu____352 =
                         let uu____355 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____355
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____352, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____345  in
                   FStar_Syntax_Syntax.mk uu____344  in
                 uu____337 FStar_Pervasives_Native.None r1  in
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
                   let uu____370 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____370
                    in
                 let hd1 =
                   let uu____372 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____372
                    in
                 let tl1 =
                   let uu____374 =
                     let uu____375 =
                       let uu____382 =
                         let uu____383 =
                           let uu____390 =
                             let uu____393 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____393
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____390, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____383  in
                       FStar_Syntax_Syntax.mk uu____382  in
                     uu____375 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____374
                    in
                 let res =
                   let uu____399 =
                     let uu____406 =
                       let uu____407 =
                         let uu____414 =
                           let uu____417 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____417
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____414,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____407  in
                     FStar_Syntax_Syntax.mk uu____406  in
                   uu____399 FStar_Pervasives_Native.None r2  in
                 let uu____420 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____420
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
               let uu____459 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____459;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = [];
                 FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
               }
           | uu____464 ->
               let err_msg =
                 let uu____469 =
                   let uu____471 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____471  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____469
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
    fun uu____496  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____496 with
          | (uvs,t) ->
              let uu____509 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____509 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 =
                     let uu____518 =
                       FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term
                         env1 t1 expected_typ1
                        in
                     match uu____518 with
                     | (t2,uu____526,g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                          t2)
                      in
                   if uvs1 = []
                   then
                     let uu____532 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____532 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____550 =
                        let uu____553 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____553
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____550)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____576 =
          let uu____577 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____577 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____576 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____602 =
          let uu____603 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____603 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____602 r
  
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
          (let uu____652 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____652
           then
             let uu____655 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____655
           else ());
          (let uu____660 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____660 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____691 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____691 FStar_List.flatten  in
               ((let uu____705 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____708 = FStar_TypeChecker_Env.should_verify env
                         in
                      Prims.op_Negation uu____708)
                    in
                 if uu____705
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
                           let uu____724 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____734,uu____735,uu____736,uu____737,uu____738)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____747 -> failwith "Impossible!"  in
                           match uu____724 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Inductive type "
                                      (Prims.op_Hat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____766 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____776,uu____777,ty_lid,uu____779,uu____780)
                               -> (data_lid, ty_lid)
                           | uu____787 -> failwith "Impossible"  in
                         match uu____766 with
                         | (data_lid,ty_lid) ->
                             let uu____795 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____798 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____798)
                                in
                             if uu____795
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Exception "
                                      (Prims.op_Hat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_haseq =
                   let skip_prims_type uu____814 =
                     let lid =
                       let ty = FStar_List.hd tcs  in
                       match ty.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_inductive_typ
                           (lid,uu____819,uu____820,uu____821,uu____822,uu____823)
                           -> lid
                       | uu____832 -> failwith "Impossible"  in
                     FStar_List.existsb
                       (fun s  ->
                          s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                       FStar_TypeChecker_TcInductive.early_prims_inductives
                      in
                   let is_noeq =
                     FStar_List.existsb
                       (fun q  -> q = FStar_Syntax_Syntax.Noeq) quals
                      in
                   let is_erasable uu____849 =
                     let uu____850 =
                       let uu____853 = FStar_List.hd tcs  in
                       uu____853.FStar_Syntax_Syntax.sigattrs  in
                     FStar_Syntax_Util.has_attribute uu____850
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
          let pop1 uu____934 =
            let uu____935 = FStar_TypeChecker_Env.pop env1 "tc_inductive"  in
            ()  in
          try
            (fun uu___206_945  ->
               match () with
               | () ->
                   let uu____952 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____952 (fun r  -> pop1 (); r)) ()
          with | uu___205_983 -> (pop1 (); FStar_Exn.raise uu___205_983)
  
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
      | uu____1299 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____1357 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____1357 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____1382 .
    'Auu____1382 FStar_Pervasives_Native.option -> 'Auu____1382 Prims.list
  =
  fun uu___0_1391  ->
    match uu___0_1391 with
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
            let uu____1471 = collect1 tl1  in
            (match uu____1471 with
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
        | ((e,n1)::uu____1709,[]) ->
            FStar_Pervasives_Native.Some (e, n1, Prims.int_zero)
        | ([],(e,n1)::uu____1765) ->
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
          let uu____1975 =
            let uu____1977 = FStar_Options.ide ()  in
            Prims.op_Negation uu____1977  in
          if uu____1975
          then
            let uu____1980 =
              let uu____1985 = FStar_TypeChecker_Env.dsenv env  in
              let uu____1986 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____1985 uu____1986  in
            (match uu____1980 with
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
                              let uu____2019 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____2020 =
                                let uu____2026 =
                                  let uu____2028 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____2030 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____2028 uu____2030
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____2026)
                                 in
                              FStar_Errors.log_issue uu____2019 uu____2020
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____2037 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____2038 =
                                   let uu____2044 =
                                     let uu____2046 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____2046
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____2044)
                                    in
                                 FStar_Errors.log_issue uu____2037 uu____2038)
                              else ())
                         else ())))
          else ()
      | uu____2056 -> ()
  
let (unembed_optionstate_knot :
  FStar_Options.optionstate FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (unembed_optionstate :
  FStar_Syntax_Syntax.term ->
    FStar_Options.optionstate FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____2086 =
      let uu____2093 =
        let uu____2096 = FStar_ST.op_Bang unembed_optionstate_knot  in
        FStar_Util.must uu____2096  in
      FStar_Syntax_Embeddings.unembed uu____2093 t  in
    uu____2086 true FStar_Syntax_Embeddings.id_norm_cb
  
let proc_check_with :
  'a . FStar_Syntax_Syntax.attribute Prims.list -> (unit -> 'a) -> 'a =
  fun attrs  ->
    fun kont  ->
      let uu____2158 =
        FStar_Syntax_Util.get_attribute FStar_Parser_Const.check_with_lid
          attrs
         in
      match uu____2158 with
      | FStar_Pervasives_Native.None  -> kont ()
      | FStar_Pervasives_Native.Some ((a,FStar_Pervasives_Native.None )::[])
          ->
          FStar_Options.with_saved_options
            (fun uu____2186  ->
               (let uu____2188 =
                  let uu____2189 = unembed_optionstate a  in
                  FStar_All.pipe_right uu____2189 FStar_Util.must  in
                FStar_Options.set uu____2188);
               kont ())
      | uu____2194 -> failwith "huh?"
  
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
        (fun uu____2245  ->
           let r = se.FStar_Syntax_Syntax.sigrng  in
           let se1 =
             let uu____2248 = FStar_Options.record_options ()  in
             if uu____2248
             then
               let uu___337_2251 = se  in
               let uu____2252 =
                 let uu____2255 = FStar_Options.peek ()  in
                 FStar_Pervasives_Native.Some uu____2255  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (uu___337_2251.FStar_Syntax_Syntax.sigel);
                 FStar_Syntax_Syntax.sigrng =
                   (uu___337_2251.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___337_2251.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___337_2251.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___337_2251.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts = uu____2252
               }
             else se  in
           match se1.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ uu____2268 ->
               failwith "Impossible bare data-constructor"
           | FStar_Syntax_Syntax.Sig_datacon uu____2296 ->
               failwith "Impossible bare data-constructor"
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
                 FStar_All.pipe_right ses
                   (FStar_List.map
                      (fun e  ->
                         let uu___356_2363 = e  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___356_2363.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___356_2363.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___356_2363.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___356_2363.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (FStar_List.append
                                e.FStar_Syntax_Syntax.sigattrs
                                se1.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___356_2363.FStar_Syntax_Syntax.sigopts)
                         }))
                  in
               let ses2 =
                 let uu____2367 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env1)
                    in
                 if uu____2367
                 then
                   let ses2 =
                     let uu____2375 =
                       let uu____2376 =
                         let uu____2377 =
                           tc_inductive
                             (let uu___360_2386 = env1  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___360_2386.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___360_2386.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___360_2386.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___360_2386.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___360_2386.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___360_2386.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___360_2386.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___360_2386.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___360_2386.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___360_2386.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___360_2386.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___360_2386.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___360_2386.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___360_2386.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___360_2386.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___360_2386.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___360_2386.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___360_2386.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___360_2386.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___360_2386.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___360_2386.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___360_2386.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___360_2386.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___360_2386.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___360_2386.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___360_2386.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___360_2386.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___360_2386.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___360_2386.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___360_2386.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___360_2386.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___360_2386.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___360_2386.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___360_2386.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___360_2386.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___360_2386.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___360_2386.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___360_2386.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___360_2386.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___360_2386.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___360_2386.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___360_2386.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___360_2386.FStar_TypeChecker_Env.erasable_types_tab)
                              }) ses1 se1.FStar_Syntax_Syntax.sigquals lids
                            in
                         FStar_All.pipe_right uu____2377
                           FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____2376
                         (FStar_TypeChecker_Normalize.elim_uvars env1)
                        in
                     FStar_All.pipe_right uu____2375
                       FStar_Syntax_Util.ses_of_sigbundle
                      in
                   ((let uu____2400 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____2400
                     then
                       let uu____2405 =
                         FStar_Syntax_Print.sigelt_to_string
                           (let uu___364_2409 = se1  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_bundle (ses2, lids));
                              FStar_Syntax_Syntax.sigrng =
                                (uu___364_2409.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___364_2409.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___364_2409.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___364_2409.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (uu___364_2409.FStar_Syntax_Syntax.sigopts)
                            })
                          in
                       FStar_Util.print1 "Inductive after phase 1: %s\n"
                         uu____2405
                     else ());
                    ses2)
                 else ses1  in
               let uu____2419 =
                 tc_inductive env1 ses2 se1.FStar_Syntax_Syntax.sigquals lids
                  in
               (match uu____2419 with
                | (sigbndle,projectors_ses) ->
                    let sigbndle1 =
                      let uu___371_2443 = sigbndle  in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___371_2443.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___371_2443.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___371_2443.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___371_2443.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (se1.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___371_2443.FStar_Syntax_Syntax.sigopts)
                      }  in
                    ([sigbndle1], projectors_ses, env0))
           | FStar_Syntax_Syntax.Sig_pragma p ->
               (FStar_Syntax_Util.process_pragma p r; ([se1], [], env0))
           | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
               let uu____2455 =
                 FStar_TypeChecker_TcEffect.dmff_cps_and_elaborate env ne  in
               (match uu____2455 with
                | (ses,ne1,lift_from_pure_opt) ->
                    let effect_and_lift_ses =
                      match lift_from_pure_opt with
                      | FStar_Pervasives_Native.Some lift ->
                          [(let uu___385_2494 = se1  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_new_effect ne1);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___385_2494.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___385_2494.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___385_2494.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___385_2494.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (uu___385_2494.FStar_Syntax_Syntax.sigopts)
                            });
                          lift]
                      | FStar_Pervasives_Native.None  ->
                          [(let uu___388_2496 = se1  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_new_effect ne1);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___388_2496.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___388_2496.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___388_2496.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___388_2496.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (uu___388_2496.FStar_Syntax_Syntax.sigopts)
                            })]
                       in
                    ([], (FStar_List.append ses effect_and_lift_ses), env0))
           | FStar_Syntax_Syntax.Sig_new_effect ne ->
               let ne1 =
                 let uu____2503 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env)
                    in
                 if uu____2503
                 then
                   let ne1 =
                     let uu____2507 =
                       let uu____2508 =
                         let uu____2509 =
                           FStar_TypeChecker_TcEffect.tc_eff_decl
                             (let uu___394_2512 = env  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___394_2512.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___394_2512.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___394_2512.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___394_2512.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___394_2512.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___394_2512.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___394_2512.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___394_2512.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___394_2512.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___394_2512.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___394_2512.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___394_2512.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___394_2512.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___394_2512.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___394_2512.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___394_2512.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___394_2512.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___394_2512.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___394_2512.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___394_2512.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___394_2512.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___394_2512.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___394_2512.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___394_2512.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___394_2512.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___394_2512.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___394_2512.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___394_2512.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___394_2512.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___394_2512.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___394_2512.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___394_2512.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___394_2512.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___394_2512.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___394_2512.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___394_2512.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___394_2512.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___394_2512.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___394_2512.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___394_2512.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___394_2512.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___394_2512.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___394_2512.FStar_TypeChecker_Env.erasable_types_tab)
                              }) ne se1.FStar_Syntax_Syntax.sigquals
                            in
                         FStar_All.pipe_right uu____2509
                           (fun ne1  ->
                              let uu___397_2518 = se1  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___397_2518.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___397_2518.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___397_2518.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___397_2518.FStar_Syntax_Syntax.sigattrs);
                                FStar_Syntax_Syntax.sigopts =
                                  (uu___397_2518.FStar_Syntax_Syntax.sigopts)
                              })
                          in
                       FStar_All.pipe_right uu____2508
                         (FStar_TypeChecker_Normalize.elim_uvars env)
                        in
                     FStar_All.pipe_right uu____2507
                       FStar_Syntax_Util.eff_decl_of_new_effect
                      in
                   ((let uu____2520 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____2520
                     then
                       let uu____2525 =
                         FStar_Syntax_Print.sigelt_to_string
                           (let uu___401_2529 = se1  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_new_effect ne1);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___401_2529.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___401_2529.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___401_2529.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___401_2529.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (uu___401_2529.FStar_Syntax_Syntax.sigopts)
                            })
                          in
                       FStar_Util.print1 "Effect decl after phase 1: %s\n"
                         uu____2525
                     else ());
                    ne1)
                 else ne  in
               let ne2 =
                 FStar_TypeChecker_TcEffect.tc_eff_decl env ne1
                   se1.FStar_Syntax_Syntax.sigquals
                  in
               let se2 =
                 let uu___406_2537 = se1  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_new_effect ne2);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___406_2537.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___406_2537.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___406_2537.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___406_2537.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (uu___406_2537.FStar_Syntax_Syntax.sigopts)
                 }  in
               ([se2], [], env0)
           | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
               let sub2 = FStar_TypeChecker_TcEffect.tc_lift env sub1 r  in
               let se2 =
                 let uu___412_2545 = se1  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___412_2545.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___412_2545.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___412_2545.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___412_2545.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (uu___412_2545.FStar_Syntax_Syntax.sigopts)
                 }  in
               ([se2], [], env)
           | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
               let uu____2559 =
                 FStar_TypeChecker_TcEffect.tc_effect_abbrev env
                   (lid, uvs, tps, c) r
                  in
               (match uu____2559 with
                | (lid1,uvs1,tps1,c1) ->
                    let se2 =
                      let uu___427_2583 = se1  in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_effect_abbrev
                             (lid1, uvs1, tps1, c1, flags));
                        FStar_Syntax_Syntax.sigrng =
                          (uu___427_2583.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___427_2583.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___427_2583.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___427_2583.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___427_2583.FStar_Syntax_Syntax.sigopts)
                      }  in
                    ([se2], [], env0))
           | FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2590,uu____2591,uu____2592) when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___1_2597  ->
                       match uu___1_2597 with
                       | FStar_Syntax_Syntax.OnlyName  -> true
                       | uu____2600 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_let (uu____2606,uu____2607) when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___1_2616  ->
                       match uu___1_2616 with
                       | FStar_Syntax_Syntax.OnlyName  -> true
                       | uu____2619 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
               let env1 = FStar_TypeChecker_Env.set_range env r  in
               ((let uu____2630 = FStar_TypeChecker_Env.lid_exists env1 lid
                    in
                 if uu____2630
                 then
                   let uu____2633 =
                     let uu____2639 =
                       let uu____2641 = FStar_Ident.text_of_lid lid  in
                       FStar_Util.format1
                         "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                         uu____2641
                        in
                     (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                       uu____2639)
                      in
                   FStar_Errors.raise_error uu____2633 r
                 else ());
                (let uu____2647 =
                   let uu____2656 =
                     (FStar_Options.use_two_phase_tc ()) &&
                       (FStar_TypeChecker_Env.should_verify env1)
                      in
                   if uu____2656
                   then
                     let uu____2667 =
                       tc_declare_typ
                         (let uu___451_2670 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___451_2670.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___451_2670.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___451_2670.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___451_2670.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___451_2670.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___451_2670.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___451_2670.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___451_2670.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___451_2670.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___451_2670.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___451_2670.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___451_2670.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___451_2670.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___451_2670.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___451_2670.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___451_2670.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___451_2670.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___451_2670.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___451_2670.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___451_2670.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___451_2670.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___451_2670.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___451_2670.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___451_2670.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___451_2670.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___451_2670.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___451_2670.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___451_2670.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___451_2670.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___451_2670.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___451_2670.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___451_2670.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___451_2670.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___451_2670.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___451_2670.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___451_2670.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___451_2670.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___451_2670.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___451_2670.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___451_2670.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___451_2670.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___451_2670.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___451_2670.FStar_TypeChecker_Env.erasable_types_tab)
                          }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng
                        in
                     match uu____2667 with
                     | (uvs1,t1) ->
                         ((let uu____2696 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "TwoPhases")
                              in
                           if uu____2696
                           then
                             let uu____2701 =
                               FStar_Syntax_Print.term_to_string t1  in
                             let uu____2703 =
                               FStar_Syntax_Print.univ_names_to_string uvs1
                                in
                             FStar_Util.print2
                               "Val declaration after phase 1: %s and uvs: %s\n"
                               uu____2701 uu____2703
                           else ());
                          (uvs1, t1))
                   else (uvs, t)  in
                 match uu____2647 with
                 | (uvs1,t1) ->
                     let uu____2738 =
                       tc_declare_typ env1 (uvs1, t1)
                         se1.FStar_Syntax_Syntax.sigrng
                        in
                     (match uu____2738 with
                      | (uvs2,t2) ->
                          ([(let uu___464_2768 = se1  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (lid, uvs2, t2));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___464_2768.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___464_2768.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___464_2768.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___464_2768.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___464_2768.FStar_Syntax_Syntax.sigopts)
                             })], [], env0))))
           | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
               let env1 = FStar_TypeChecker_Env.set_range env r  in
               let uu____2773 =
                 let uu____2782 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env1)
                    in
                 if uu____2782
                 then
                   let uu____2793 =
                     tc_assume
                       (let uu___473_2796 = env1  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___473_2796.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___473_2796.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___473_2796.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___473_2796.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___473_2796.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___473_2796.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___473_2796.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___473_2796.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___473_2796.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___473_2796.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___473_2796.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___473_2796.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___473_2796.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___473_2796.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level =
                            (uu___473_2796.FStar_TypeChecker_Env.top_level);
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___473_2796.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___473_2796.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___473_2796.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___473_2796.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax = true;
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___473_2796.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 = true;
                          FStar_TypeChecker_Env.failhard =
                            (uu___473_2796.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___473_2796.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___473_2796.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___473_2796.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___473_2796.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___473_2796.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___473_2796.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___473_2796.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___473_2796.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___473_2796.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___473_2796.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___473_2796.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___473_2796.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.try_solve_implicits_hook =
                            (uu___473_2796.FStar_TypeChecker_Env.try_solve_implicits_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___473_2796.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___473_2796.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___473_2796.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___473_2796.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___473_2796.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___473_2796.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___473_2796.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___473_2796.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (uu___473_2796.FStar_TypeChecker_Env.erasable_types_tab)
                        }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng
                      in
                   match uu____2793 with
                   | (uvs1,t1) ->
                       ((let uu____2822 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "TwoPhases")
                            in
                         if uu____2822
                         then
                           let uu____2827 =
                             FStar_Syntax_Print.term_to_string t1  in
                           let uu____2829 =
                             FStar_Syntax_Print.univ_names_to_string uvs1  in
                           FStar_Util.print2
                             "Assume after phase 1: %s and uvs: %s\n"
                             uu____2827 uu____2829
                         else ());
                        (uvs1, t1))
                 else (uvs, t)  in
               (match uu____2773 with
                | (uvs1,t1) ->
                    let uu____2864 =
                      tc_assume env1 (uvs1, t1)
                        se1.FStar_Syntax_Syntax.sigrng
                       in
                    (match uu____2864 with
                     | (uvs2,t2) ->
                         ([(let uu___486_2894 = se1  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_assume
                                   (lid, uvs2, t2));
                              FStar_Syntax_Syntax.sigrng =
                                (uu___486_2894.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___486_2894.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___486_2894.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___486_2894.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (uu___486_2894.FStar_Syntax_Syntax.sigopts)
                            })], [], env0)))
           | FStar_Syntax_Syntax.Sig_main e ->
               let env1 = FStar_TypeChecker_Env.set_range env r  in
               let env2 =
                 FStar_TypeChecker_Env.set_expected_typ env1
                   FStar_Syntax_Syntax.t_unit
                  in
               let uu____2898 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
               (match uu____2898 with
                | (e1,c,g1) ->
                    let uu____2918 =
                      let uu____2925 = FStar_TypeChecker_Common.lcomp_comp c
                         in
                      match uu____2925 with
                      | (c1,g_lc) ->
                          let uu____2938 =
                            let uu____2945 =
                              let uu____2948 =
                                FStar_Syntax_Util.ml_comp
                                  FStar_Syntax_Syntax.t_unit r
                                 in
                              FStar_Pervasives_Native.Some uu____2948  in
                            FStar_TypeChecker_TcTerm.check_expected_effect
                              env2 uu____2945 (e1, c1)
                             in
                          (match uu____2938 with
                           | (e2,_x,g) ->
                               let uu____2958 =
                                 FStar_TypeChecker_Env.conj_guard g_lc g  in
                               (e2, _x, uu____2958))
                       in
                    (match uu____2918 with
                     | (e2,uu____2970,g) ->
                         ((let uu____2973 =
                             FStar_TypeChecker_Env.conj_guard g1 g  in
                           FStar_TypeChecker_Rel.force_trivial_guard env2
                             uu____2973);
                          (let se2 =
                             let uu___508_2975 = se1  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_main e2);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___508_2975.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___508_2975.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___508_2975.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___508_2975.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___508_2975.FStar_Syntax_Syntax.sigopts)
                             }  in
                           ([se2], [], env0)))))
           | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
               ((let uu____2987 = FStar_Options.debug_any ()  in
                 if uu____2987
                 then
                   let uu____2990 =
                     FStar_Ident.string_of_lid
                       env.FStar_TypeChecker_Env.curmodule
                      in
                   let uu____2992 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print2 "%s: Found splice of (%s)\n" uu____2990
                     uu____2992
                 else ());
                (let uu____2997 = FStar_TypeChecker_TcTerm.tc_tactic env t
                    in
                 match uu____2997 with
                 | (t1,uu____3015,g) ->
                     (FStar_TypeChecker_Rel.force_trivial_guard env g;
                      (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                       let lids' =
                         FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                           ses
                          in
                       FStar_List.iter
                         (fun lid  ->
                            let uu____3029 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids'
                               in
                            match uu____3029 with
                            | FStar_Pervasives_Native.None  when
                                Prims.op_Negation
                                  env.FStar_TypeChecker_Env.nosynth
                                ->
                                let uu____3032 =
                                  let uu____3038 =
                                    let uu____3040 =
                                      FStar_Ident.string_of_lid lid  in
                                    let uu____3042 =
                                      let uu____3044 =
                                        FStar_List.map
                                          FStar_Ident.string_of_lid lids'
                                         in
                                      FStar_All.pipe_left
                                        (FStar_String.concat ", ") uu____3044
                                       in
                                    FStar_Util.format2
                                      "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                      uu____3040 uu____3042
                                     in
                                  (FStar_Errors.Fatal_SplicedUndef,
                                    uu____3038)
                                   in
                                FStar_Errors.raise_error uu____3032 r
                            | uu____3056 -> ()) lids;
                       (let dsenv1 =
                          FStar_List.fold_left
                            FStar_Syntax_DsEnv.push_sigelt_force
                            env.FStar_TypeChecker_Env.dsenv ses
                           in
                        let env1 =
                          let uu___529_3061 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___529_3061.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___529_3061.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___529_3061.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___529_3061.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___529_3061.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___529_3061.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___529_3061.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___529_3061.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___529_3061.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___529_3061.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___529_3061.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___529_3061.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___529_3061.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___529_3061.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___529_3061.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___529_3061.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___529_3061.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___529_3061.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___529_3061.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___529_3061.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___529_3061.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___529_3061.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___529_3061.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___529_3061.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___529_3061.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___529_3061.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___529_3061.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___529_3061.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___529_3061.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___529_3061.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___529_3061.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___529_3061.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___529_3061.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___529_3061.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___529_3061.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___529_3061.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___529_3061.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___529_3061.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___529_3061.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___529_3061.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___529_3061.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv = dsenv1;
                            FStar_TypeChecker_Env.nbe =
                              (uu___529_3061.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___529_3061.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___529_3061.FStar_TypeChecker_Env.erasable_types_tab)
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
                     let uu____3129 =
                       let uu____3131 =
                         let uu____3140 = drop_logic val_q  in
                         let uu____3143 = drop_logic q'  in
                         (uu____3140, uu____3143)  in
                       match uu____3131 with
                       | (val_q1,q'1) ->
                           ((FStar_List.length val_q1) =
                              (FStar_List.length q'1))
                             &&
                             (FStar_List.forall2
                                FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                        in
                     if uu____3129
                     then FStar_Pervasives_Native.Some q'
                     else
                       (let uu____3170 =
                          let uu____3176 =
                            let uu____3178 =
                              FStar_Syntax_Print.lid_to_string l  in
                            let uu____3180 =
                              FStar_Syntax_Print.quals_to_string val_q  in
                            let uu____3182 =
                              FStar_Syntax_Print.quals_to_string q'  in
                            FStar_Util.format3
                              "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                              uu____3178 uu____3180 uu____3182
                             in
                          (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                            uu____3176)
                           in
                        FStar_Errors.raise_error uu____3170 r)
                  in
               let rename_parameters lb =
                 let rename_in_typ def typ =
                   let typ1 = FStar_Syntax_Subst.compress typ  in
                   let def_bs =
                     let uu____3219 =
                       let uu____3220 = FStar_Syntax_Subst.compress def  in
                       uu____3220.FStar_Syntax_Syntax.n  in
                     match uu____3219 with
                     | FStar_Syntax_Syntax.Tm_abs
                         (binders,uu____3232,uu____3233) -> binders
                     | uu____3258 -> []  in
                   match typ1 with
                   | {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                         (val_bs,c);
                       FStar_Syntax_Syntax.pos = r1;
                       FStar_Syntax_Syntax.vars = uu____3270;_} ->
                       let has_auto_name bv =
                         FStar_Util.starts_with
                           (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                           FStar_Ident.reserved_prefix
                          in
                       let rec rename_binders1 def_bs1 val_bs1 =
                         match (def_bs1, val_bs1) with
                         | ([],uu____3375) -> val_bs1
                         | (uu____3406,[]) -> val_bs1
                         | ((body_bv,uu____3438)::bt,(val_bv,aqual)::vt) ->
                             let uu____3495 = rename_binders1 bt vt  in
                             ((match ((has_auto_name body_bv),
                                       (has_auto_name val_bv))
                               with
                               | (true ,uu____3519) -> (val_bv, aqual)
                               | (false ,true ) ->
                                   ((let uu___598_3533 = val_bv  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (let uu___600_3536 =
                                            val_bv.FStar_Syntax_Syntax.ppname
                                             in
                                          {
                                            FStar_Ident.idText =
                                              ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                            FStar_Ident.idRange =
                                              (uu___600_3536.FStar_Ident.idRange)
                                          });
                                       FStar_Syntax_Syntax.index =
                                         (uu___598_3533.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (uu___598_3533.FStar_Syntax_Syntax.sort)
                                     }), aqual)
                               | (false ,false ) -> (val_bv, aqual))) ::
                               uu____3495
                          in
                       let uu____3543 =
                         let uu____3550 =
                           let uu____3551 =
                             let uu____3566 = rename_binders1 def_bs val_bs
                                in
                             (uu____3566, c)  in
                           FStar_Syntax_Syntax.Tm_arrow uu____3551  in
                         FStar_Syntax_Syntax.mk uu____3550  in
                       uu____3543 FStar_Pervasives_Native.None r1
                   | uu____3585 -> typ1  in
                 let uu___606_3586 = lb  in
                 let uu____3587 =
                   rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                     lb.FStar_Syntax_Syntax.lbtyp
                    in
                 {
                   FStar_Syntax_Syntax.lbname =
                     (uu___606_3586.FStar_Syntax_Syntax.lbname);
                   FStar_Syntax_Syntax.lbunivs =
                     (uu___606_3586.FStar_Syntax_Syntax.lbunivs);
                   FStar_Syntax_Syntax.lbtyp = uu____3587;
                   FStar_Syntax_Syntax.lbeff =
                     (uu___606_3586.FStar_Syntax_Syntax.lbeff);
                   FStar_Syntax_Syntax.lbdef =
                     (uu___606_3586.FStar_Syntax_Syntax.lbdef);
                   FStar_Syntax_Syntax.lbattrs =
                     (uu___606_3586.FStar_Syntax_Syntax.lbattrs);
                   FStar_Syntax_Syntax.lbpos =
                     (uu___606_3586.FStar_Syntax_Syntax.lbpos)
                 }  in
               let uu____3590 =
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.fold_left
                      (fun uu____3645  ->
                         fun lb  ->
                           match uu____3645 with
                           | (gen1,lbs1,quals_opt) ->
                               let lbname =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu____3691 =
                                 let uu____3703 =
                                   FStar_TypeChecker_Env.try_lookup_val_decl
                                     env1
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 match uu____3703 with
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
                                       | uu____3783 ->
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
                                      (let uu____3830 =
                                         FStar_Syntax_Syntax.mk_lb
                                           ((FStar_Util.Inr lbname), uvs,
                                             FStar_Parser_Const.effect_ALL_lid,
                                             tval, def, [],
                                             (lb.FStar_Syntax_Syntax.lbpos))
                                          in
                                       (false, uu____3830, quals_opt1)))
                                  in
                               (match uu____3691 with
                                | (gen2,lb1,quals_opt1) ->
                                    (gen2, (lb1 :: lbs1), quals_opt1)))
                      (true, [],
                        (if se1.FStar_Syntax_Syntax.sigquals = []
                         then FStar_Pervasives_Native.None
                         else
                           FStar_Pervasives_Native.Some
                             (se1.FStar_Syntax_Syntax.sigquals))))
                  in
               (match uu____3590 with
                | (should_generalize,lbs',quals_opt) ->
                    let quals =
                      match quals_opt with
                      | FStar_Pervasives_Native.None  ->
                          [FStar_Syntax_Syntax.Visible_default]
                      | FStar_Pervasives_Native.Some q ->
                          let uu____3934 =
                            FStar_All.pipe_right q
                              (FStar_Util.for_some
                                 (fun uu___2_3940  ->
                                    match uu___2_3940 with
                                    | FStar_Syntax_Syntax.Irreducible  ->
                                        true
                                    | FStar_Syntax_Syntax.Visible_default  ->
                                        true
                                    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                         -> true
                                    | uu____3945 -> false))
                             in
                          if uu____3934
                          then q
                          else FStar_Syntax_Syntax.Visible_default :: q
                       in
                    let lbs'1 = FStar_List.rev lbs'  in
                    let e =
                      let uu____3958 =
                        let uu____3965 =
                          let uu____3966 =
                            let uu____3980 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   FStar_Const.Const_unit)
                                FStar_Pervasives_Native.None r
                               in
                            (((FStar_Pervasives_Native.fst lbs), lbs'1),
                              uu____3980)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____3966  in
                        FStar_Syntax_Syntax.mk uu____3965  in
                      uu____3958 FStar_Pervasives_Native.None r  in
                    let env' =
                      let uu___649_3999 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___649_3999.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___649_3999.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___649_3999.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___649_3999.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___649_3999.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___649_3999.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___649_3999.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___649_3999.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___649_3999.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___649_3999.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___649_3999.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___649_3999.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize = should_generalize;
                        FStar_TypeChecker_Env.letrecs =
                          (uu___649_3999.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level = true;
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___649_3999.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___649_3999.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___649_3999.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___649_3999.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___649_3999.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___649_3999.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___649_3999.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___649_3999.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___649_3999.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___649_3999.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___649_3999.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___649_3999.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___649_3999.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___649_3999.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___649_3999.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___649_3999.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___649_3999.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___649_3999.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___649_3999.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___649_3999.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.try_solve_implicits_hook =
                          (uu___649_3999.FStar_TypeChecker_Env.try_solve_implicits_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___649_3999.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___649_3999.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___649_3999.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___649_3999.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___649_3999.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___649_3999.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___649_3999.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___649_3999.FStar_TypeChecker_Env.strict_args_tab);
                        FStar_TypeChecker_Env.erasable_types_tab =
                          (uu___649_3999.FStar_TypeChecker_Env.erasable_types_tab)
                      }  in
                    let e1 =
                      let uu____4002 =
                        (FStar_Options.use_two_phase_tc ()) &&
                          (FStar_TypeChecker_Env.should_verify env')
                         in
                      if uu____4002
                      then
                        let drop_lbtyp e_lax =
                          let uu____4011 =
                            let uu____4012 =
                              FStar_Syntax_Subst.compress e_lax  in
                            uu____4012.FStar_Syntax_Syntax.n  in
                          match uu____4011 with
                          | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2)
                              ->
                              let lb_unannotated =
                                let uu____4034 =
                                  let uu____4035 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____4035.FStar_Syntax_Syntax.n  in
                                match uu____4034 with
                                | FStar_Syntax_Syntax.Tm_let
                                    ((uu____4039,lb1::[]),uu____4041) ->
                                    let uu____4057 =
                                      let uu____4058 =
                                        FStar_Syntax_Subst.compress
                                          lb1.FStar_Syntax_Syntax.lbtyp
                                         in
                                      uu____4058.FStar_Syntax_Syntax.n  in
                                    (match uu____4057 with
                                     | FStar_Syntax_Syntax.Tm_unknown  ->
                                         true
                                     | uu____4063 -> false)
                                | uu____4065 ->
                                    failwith
                                      "Impossible: first phase lb and second phase lb differ in structure!"
                                 in
                              if lb_unannotated
                              then
                                let uu___674_4069 = e_lax  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_let
                                       ((false,
                                          [(let uu___676_4084 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___676_4084.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___676_4084.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                FStar_Syntax_Syntax.tun;
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___676_4084.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___676_4084.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___676_4084.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___676_4084.FStar_Syntax_Syntax.lbpos)
                                            })]), e2));
                                  FStar_Syntax_Syntax.pos =
                                    (uu___674_4069.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___674_4069.FStar_Syntax_Syntax.vars)
                                }
                              else e_lax
                          | uu____4087 -> e_lax  in
                        let uu____4088 =
                          FStar_Util.record_time
                            (fun uu____4096  ->
                               let uu____4097 =
                                 let uu____4098 =
                                   let uu____4099 =
                                     FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                       (let uu___680_4108 = env'  in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___680_4108.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___680_4108.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___680_4108.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___680_4108.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___680_4108.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___680_4108.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___680_4108.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___680_4108.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___680_4108.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___680_4108.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___680_4108.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___680_4108.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___680_4108.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___680_4108.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___680_4108.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___680_4108.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            (uu___680_4108.FStar_TypeChecker_Env.use_eq);
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___680_4108.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___680_4108.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax = true;
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___680_4108.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 = true;
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___680_4108.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___680_4108.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___680_4108.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___680_4108.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___680_4108.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___680_4108.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___680_4108.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___680_4108.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___680_4108.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___680_4108.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___680_4108.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___680_4108.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___680_4108.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.try_solve_implicits_hook
                                            =
                                            (uu___680_4108.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___680_4108.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___680_4108.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.is_native_tactic
                                            =
                                            (uu___680_4108.FStar_TypeChecker_Env.is_native_tactic);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___680_4108.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___680_4108.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___680_4108.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___680_4108.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___680_4108.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (uu___680_4108.FStar_TypeChecker_Env.erasable_types_tab)
                                        }) e
                                      in
                                   FStar_All.pipe_right uu____4099
                                     (fun uu____4121  ->
                                        match uu____4121 with
                                        | (e1,uu____4129,uu____4130) -> e1)
                                    in
                                 FStar_All.pipe_right uu____4098
                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                      env')
                                  in
                               FStar_All.pipe_right uu____4097 drop_lbtyp)
                           in
                        match uu____4088 with
                        | (e1,ms) ->
                            ((let uu____4136 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "TwoPhases")
                                 in
                              if uu____4136
                              then
                                let uu____4141 =
                                  FStar_Syntax_Print.term_to_string e1  in
                                FStar_Util.print1
                                  "Let binding after phase 1: %s\n"
                                  uu____4141
                              else ());
                             (let uu____4147 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "TCDeclTime")
                                 in
                              if uu____4147
                              then
                                let uu____4152 = FStar_Util.string_of_int ms
                                   in
                                FStar_Util.print1
                                  "Let binding elaborated (phase 1) in %s milliseconds\n"
                                  uu____4152
                              else ());
                             e1)
                      else e  in
                    let uu____4159 =
                      let uu____4168 =
                        FStar_Syntax_Util.extract_attr'
                          FStar_Parser_Const.postprocess_with
                          se1.FStar_Syntax_Syntax.sigattrs
                         in
                      match uu____4168 with
                      | FStar_Pervasives_Native.None  ->
                          ((se1.FStar_Syntax_Syntax.sigattrs),
                            FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some
                          (ats,(tau,FStar_Pervasives_Native.None )::[]) ->
                          (ats, (FStar_Pervasives_Native.Some tau))
                      | FStar_Pervasives_Native.Some (ats,args) ->
                          (FStar_Errors.log_issue r
                             (FStar_Errors.Warning_UnrecognizedAttribute,
                               "Ill-formed application of `postprocess_with`");
                           ((se1.FStar_Syntax_Syntax.sigattrs),
                             FStar_Pervasives_Native.None))
                       in
                    (match uu____4159 with
                     | (attrs,post_tau) ->
                         let se2 =
                           let uu___710_4273 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___710_4273.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___710_4273.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___710_4273.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___710_4273.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs = attrs;
                             FStar_Syntax_Syntax.sigopts =
                               (uu___710_4273.FStar_Syntax_Syntax.sigopts)
                           }  in
                         let postprocess_lb tau lb =
                           let lbdef =
                             env1.FStar_TypeChecker_Env.postprocess env1 tau
                               lb.FStar_Syntax_Syntax.lbtyp
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           let uu___717_4286 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___717_4286.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___717_4286.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___717_4286.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___717_4286.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = lbdef;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___717_4286.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___717_4286.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let uu____4287 =
                           FStar_Util.record_time
                             (fun uu____4306  ->
                                FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                  env' e1)
                            in
                         (match uu____4287 with
                          | (r1,ms) ->
                              ((let uu____4334 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env1)
                                    (FStar_Options.Other "TCDeclTime")
                                   in
                                if uu____4334
                                then
                                  let uu____4339 =
                                    FStar_Util.string_of_int ms  in
                                  FStar_Util.print1
                                    "Let binding typechecked in phase 2 in %s milliseconds\n"
                                    uu____4339
                                else ());
                               (let uu____4344 =
                                  match r1 with
                                  | ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                                       FStar_Syntax_Syntax.pos = uu____4369;
                                       FStar_Syntax_Syntax.vars = uu____4370;_},uu____4371,g)
                                      when FStar_TypeChecker_Env.is_trivial g
                                      ->
                                      let lbs2 =
                                        let uu____4401 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.snd lbs1)
                                            (FStar_List.map rename_parameters)
                                           in
                                        ((FStar_Pervasives_Native.fst lbs1),
                                          uu____4401)
                                         in
                                      let lbs3 =
                                        let uu____4425 =
                                          match post_tau with
                                          | FStar_Pervasives_Native.Some tau
                                              ->
                                              FStar_List.map
                                                (postprocess_lb tau)
                                                (FStar_Pervasives_Native.snd
                                                   lbs2)
                                          | FStar_Pervasives_Native.None  ->
                                              FStar_Pervasives_Native.snd
                                                lbs2
                                           in
                                        ((FStar_Pervasives_Native.fst lbs2),
                                          uu____4425)
                                         in
                                      let quals1 =
                                        match e2.FStar_Syntax_Syntax.n with
                                        | FStar_Syntax_Syntax.Tm_meta
                                            (uu____4448,FStar_Syntax_Syntax.Meta_desugared
                                             (FStar_Syntax_Syntax.Masked_effect
                                             ))
                                            ->
                                            FStar_Syntax_Syntax.HasMaskedEffect
                                            :: quals
                                        | uu____4453 -> quals  in
                                      ((let uu___747_4462 = se2  in
                                        {
                                          FStar_Syntax_Syntax.sigel =
                                            (FStar_Syntax_Syntax.Sig_let
                                               (lbs3, lids));
                                          FStar_Syntax_Syntax.sigrng =
                                            (uu___747_4462.FStar_Syntax_Syntax.sigrng);
                                          FStar_Syntax_Syntax.sigquals =
                                            quals1;
                                          FStar_Syntax_Syntax.sigmeta =
                                            (uu___747_4462.FStar_Syntax_Syntax.sigmeta);
                                          FStar_Syntax_Syntax.sigattrs =
                                            (uu___747_4462.FStar_Syntax_Syntax.sigattrs);
                                          FStar_Syntax_Syntax.sigopts =
                                            (uu___747_4462.FStar_Syntax_Syntax.sigopts)
                                        }), lbs3)
                                  | uu____4465 ->
                                      failwith
                                        "impossible (typechecking should preserve Tm_let)"
                                   in
                                match uu____4344 with
                                | (se3,lbs1) ->
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
                                     (let uu____4521 = log env1  in
                                      if uu____4521
                                      then
                                        let uu____4524 =
                                          let uu____4526 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.snd
                                                 lbs1)
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let should_log =
                                                      let uu____4546 =
                                                        let uu____4555 =
                                                          let uu____4556 =
                                                            let uu____4559 =
                                                              FStar_Util.right
                                                                lb.FStar_Syntax_Syntax.lbname
                                                               in
                                                            uu____4559.FStar_Syntax_Syntax.fv_name
                                                             in
                                                          uu____4556.FStar_Syntax_Syntax.v
                                                           in
                                                        FStar_TypeChecker_Env.try_lookup_val_decl
                                                          env1 uu____4555
                                                         in
                                                      match uu____4546 with
                                                      | FStar_Pervasives_Native.None
                                                           -> true
                                                      | uu____4568 -> false
                                                       in
                                                    if should_log
                                                    then
                                                      let uu____4580 =
                                                        FStar_Syntax_Print.lbname_to_string
                                                          lb.FStar_Syntax_Syntax.lbname
                                                         in
                                                      let uu____4582 =
                                                        FStar_Syntax_Print.term_to_string
                                                          lb.FStar_Syntax_Syntax.lbtyp
                                                         in
                                                      FStar_Util.format2
                                                        "let %s : %s"
                                                        uu____4580 uu____4582
                                                    else ""))
                                             in
                                          FStar_All.pipe_right uu____4526
                                            (FStar_String.concat "\n")
                                           in
                                        FStar_Util.print1 "%s\n" uu____4524
                                      else ());
                                     check_must_erase_attribute env0 se3;
                                     ([se3], [], env0))))))))
  
let (tc_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun se  ->
      let env1 = set_hint_correlator env se  in
      (let uu____4634 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____4634
       then
         let uu____4637 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____4637
       else ());
      (let uu____4642 = get_fail_se se  in
       match uu____4642 with
       | FStar_Pervasives_Native.Some (uu____4663,false ) when
           let uu____4680 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____4680 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___778_4706 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___778_4706.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___778_4706.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___778_4706.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___778_4706.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___778_4706.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___778_4706.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___778_4706.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___778_4706.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___778_4706.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___778_4706.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___778_4706.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___778_4706.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___778_4706.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___778_4706.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___778_4706.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___778_4706.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___778_4706.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___778_4706.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___778_4706.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___778_4706.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___778_4706.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___778_4706.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___778_4706.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___778_4706.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___778_4706.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___778_4706.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___778_4706.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___778_4706.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___778_4706.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___778_4706.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___778_4706.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___778_4706.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___778_4706.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___778_4706.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.try_solve_implicits_hook =
                   (uu___778_4706.FStar_TypeChecker_Env.try_solve_implicits_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___778_4706.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___778_4706.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___778_4706.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___778_4706.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___778_4706.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___778_4706.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___778_4706.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___778_4706.FStar_TypeChecker_Env.strict_args_tab);
                 FStar_TypeChecker_Env.erasable_types_tab =
                   (uu___778_4706.FStar_TypeChecker_Env.erasable_types_tab)
               }
             else env1  in
           ((let uu____4711 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____4711
             then
               let uu____4714 =
                 let uu____4716 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____4716
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____4714
             else ());
            (let uu____4730 =
               FStar_Errors.catch_errors
                 (fun uu____4760  ->
                    FStar_Options.with_saved_options
                      (fun uu____4772  -> tc_decl' env' se))
                in
             match uu____4730 with
             | (errs,uu____4784) ->
                 ((let uu____4814 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____4814
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____4849 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____4849  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____4861 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____4872 =
                            let uu____4882 = check_multi_eq errnos1 actual
                               in
                            match uu____4882 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- Prims.int_one), (~- Prims.int_one),
                                  (~- Prims.int_one))
                             in
                          (match uu____4872 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____4947 =
                                   let uu____4953 =
                                     let uu____4955 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____4958 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____4961 =
                                       FStar_Util.string_of_int e  in
                                     let uu____4963 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____4965 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____4955 uu____4958 uu____4961
                                       uu____4963 uu____4965
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____4953)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____4947)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____4992 .
    'Auu____4992 ->
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
               (fun uu___3_5035  ->
                  match uu___3_5035 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____5038 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____5049) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____5057 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____5067 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____5072 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____5088 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____5114 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5140) ->
            let uu____5149 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____5149
            then
              let for_export_bundle se1 uu____5186 =
                match uu____5186 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____5225,uu____5226) ->
                         let dec =
                           let uu___854_5236 = se1  in
                           let uu____5237 =
                             let uu____5238 =
                               let uu____5245 =
                                 let uu____5246 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____5246  in
                               (l, us, uu____5245)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____5238
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____5237;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___854_5236.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___854_5236.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___854_5236.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___854_5236.FStar_Syntax_Syntax.sigopts)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____5256,uu____5257,uu____5258) ->
                         let dec =
                           let uu___865_5266 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___865_5266.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___865_5266.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___865_5266.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___865_5266.FStar_Syntax_Syntax.sigopts)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____5271 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume (uu____5294,uu____5295,uu____5296)
            ->
            let uu____5297 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____5297 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____5321 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____5321
            then
              ([(let uu___881_5340 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___881_5340.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___881_5340.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___881_5340.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (uu___881_5340.FStar_Syntax_Syntax.sigopts)
                 })], (l :: hidden))
            else
              (let uu____5343 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_5349  ->
                         match uu___4_5349 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____5352 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____5358 ->
                             true
                         | uu____5360 -> false))
                  in
               if uu____5343 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____5381 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____5386 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5391 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____5396 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____5401 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____5419) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____5433 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____5433
            then ([], hidden)
            else
              (let dec =
                 let uu____5454 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____5454;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = [];
                   FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____5465 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____5465
            then
              let uu____5476 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___918_5490 = se  in
                        let uu____5491 =
                          let uu____5492 =
                            let uu____5499 =
                              let uu____5500 =
                                let uu____5503 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____5503.FStar_Syntax_Syntax.fv_name  in
                              uu____5500.FStar_Syntax_Syntax.v  in
                            (uu____5499, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____5492  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____5491;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___918_5490.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___918_5490.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___918_5490.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___918_5490.FStar_Syntax_Syntax.sigopts)
                        }))
                 in
              (uu____5476, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> Prims.bool -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      fun from_cache  ->
        (let uu____5533 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____5533
         then
           let uu____5536 = FStar_Syntax_Print.sigelt_to_string se  in
           let uu____5538 = FStar_Util.string_of_bool from_cache  in
           FStar_Util.print2
             ">>>>>>>>>>>>>>Adding top-level decl to environment: %s (from_cache:%s)\n"
             uu____5536 uu____5538
         else ());
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____5543 ->
             let uu____5560 =
               let uu____5566 =
                 let uu____5568 = FStar_Syntax_Print.sigelt_to_string se  in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____5568
                  in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____5566)  in
             FStar_Errors.raise_error uu____5560
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_datacon uu____5572 ->
             let uu____5588 =
               let uu____5594 =
                 let uu____5596 = FStar_Syntax_Print.sigelt_to_string se  in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____5596
                  in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____5594)  in
             FStar_Errors.raise_error uu____5588
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_declare_typ
             (uu____5600,uu____5601,uu____5602) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___5_5607  ->
                     match uu___5_5607 with
                     | FStar_Syntax_Syntax.OnlyName  -> true
                     | uu____5610 -> false))
             -> env
         | FStar_Syntax_Syntax.Sig_let (uu____5612,uu____5613) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___5_5622  ->
                     match uu___5_5622 with
                     | FStar_Syntax_Syntax.OnlyName  -> true
                     | uu____5625 -> false))
             -> env
         | uu____5627 ->
             let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PushOptions uu____5629) ->
                  if from_cache
                  then env1
                  else
                    (let uu___955_5636 = env1  in
                     let uu____5637 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___955_5636.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___955_5636.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___955_5636.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___955_5636.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___955_5636.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___955_5636.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___955_5636.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___955_5636.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___955_5636.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___955_5636.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___955_5636.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___955_5636.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___955_5636.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___955_5636.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___955_5636.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___955_5636.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___955_5636.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___955_5636.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___955_5636.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___955_5636.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___955_5636.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___955_5636.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___955_5636.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___955_5636.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___955_5636.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___955_5636.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___955_5636.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___955_5636.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___955_5636.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___955_5636.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___955_5636.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___955_5636.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___955_5636.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5637;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___955_5636.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___955_5636.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___955_5636.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___955_5636.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___955_5636.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___955_5636.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___955_5636.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___955_5636.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___955_5636.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___955_5636.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___955_5636.FStar_TypeChecker_Env.erasable_types_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PopOptions ) ->
                  if from_cache
                  then env1
                  else
                    (let uu___955_5641 = env1  in
                     let uu____5642 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___955_5641.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___955_5641.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___955_5641.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___955_5641.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___955_5641.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___955_5641.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___955_5641.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___955_5641.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___955_5641.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___955_5641.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___955_5641.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___955_5641.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___955_5641.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___955_5641.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___955_5641.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___955_5641.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___955_5641.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___955_5641.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___955_5641.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___955_5641.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___955_5641.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___955_5641.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___955_5641.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___955_5641.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___955_5641.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___955_5641.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___955_5641.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___955_5641.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___955_5641.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___955_5641.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___955_5641.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___955_5641.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___955_5641.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5642;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___955_5641.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___955_5641.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___955_5641.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___955_5641.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___955_5641.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___955_5641.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___955_5641.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___955_5641.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___955_5641.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___955_5641.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___955_5641.FStar_TypeChecker_Env.erasable_types_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.SetOptions uu____5643) ->
                  if from_cache
                  then env1
                  else
                    (let uu___955_5648 = env1  in
                     let uu____5649 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___955_5648.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___955_5648.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___955_5648.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___955_5648.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___955_5648.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___955_5648.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___955_5648.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___955_5648.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___955_5648.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___955_5648.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___955_5648.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___955_5648.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___955_5648.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___955_5648.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___955_5648.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___955_5648.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___955_5648.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___955_5648.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___955_5648.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___955_5648.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___955_5648.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___955_5648.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___955_5648.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___955_5648.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___955_5648.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___955_5648.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___955_5648.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___955_5648.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___955_5648.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___955_5648.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___955_5648.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___955_5648.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___955_5648.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5649;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___955_5648.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___955_5648.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___955_5648.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___955_5648.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___955_5648.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___955_5648.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___955_5648.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___955_5648.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___955_5648.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___955_5648.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___955_5648.FStar_TypeChecker_Env.erasable_types_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.ResetOptions uu____5650) ->
                  if from_cache
                  then env1
                  else
                    (let uu___955_5657 = env1  in
                     let uu____5658 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___955_5657.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___955_5657.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___955_5657.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___955_5657.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___955_5657.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___955_5657.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___955_5657.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___955_5657.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___955_5657.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___955_5657.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___955_5657.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___955_5657.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___955_5657.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___955_5657.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___955_5657.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___955_5657.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___955_5657.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___955_5657.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___955_5657.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___955_5657.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___955_5657.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___955_5657.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___955_5657.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___955_5657.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___955_5657.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___955_5657.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___955_5657.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___955_5657.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___955_5657.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___955_5657.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___955_5657.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___955_5657.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___955_5657.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5658;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___955_5657.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___955_5657.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___955_5657.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___955_5657.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___955_5657.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___955_5657.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___955_5657.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___955_5657.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___955_5657.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___955_5657.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___955_5657.FStar_TypeChecker_Env.erasable_types_tab)
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
                            let uu____5674 =
                              FStar_Syntax_Util.action_as_lb
                                ne.FStar_Syntax_Syntax.mname a
                                (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Env.push_sigelt env3 uu____5674)
                       env2)
              | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
                  let uu____5676 =
                    FStar_TypeChecker_Util.get_mlift_for_subeff env1 sub1  in
                  FStar_TypeChecker_Env.update_effect_lattice env1
                    sub1.FStar_Syntax_Syntax.source
                    sub1.FStar_Syntax_Syntax.target uu____5676
              | uu____5677 -> env1))
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____5746 se =
        match uu____5746 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____5799 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____5799
              then
                let uu____5802 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____5802
              else ());
             (let uu____5807 = tc_decl env1 se  in
              match uu____5807 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____5860 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____5860
                             then
                               let uu____5864 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____5864
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____5880 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____5880
                             then
                               let uu____5884 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____5884
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
                    (let uu____5902 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____5902
                     then
                       let uu____5907 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____5916 =
                                  let uu____5918 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____5918 "\n"  in
                                Prims.op_Hat s uu____5916) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____5907
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____5928 =
                       let uu____5937 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____5937
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____5979 se1 =
                            match uu____5979 with
                            | (exports1,hidden1) ->
                                let uu____6007 = for_export env3 hidden1 se1
                                   in
                                (match uu____6007 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____5928 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____6161 = acc  in
        match uu____6161 with
        | (uu____6196,uu____6197,env1,uu____6199) ->
            let r =
              let uu____6233 =
                let uu____6237 =
                  let uu____6239 = FStar_TypeChecker_Env.current_module env1
                     in
                  FStar_Ident.string_of_lid uu____6239  in
                FStar_Pervasives_Native.Some uu____6237  in
              FStar_Profiling.profile
                (fun uu____6262  -> process_one_decl acc se) uu____6233
                "FStar.TypeChecker.Tc.process_one_decl"
               in
            ((let uu____6265 = FStar_Options.profile_group_by_decls ()  in
              if uu____6265
              then
                let tag =
                  match FStar_Syntax_Util.lids_of_sigelt se with
                  | hd1::uu____6272 -> FStar_Ident.string_of_lid hd1
                  | uu____6275 ->
                      FStar_Range.string_of_range
                        (FStar_Syntax_Util.range_of_sigelt se)
                   in
                FStar_Profiling.report_and_clear tag
              else ());
             r)
         in
      let uu____6280 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____6280 with
      | (ses1,exports,env1,uu____6328) ->
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
          let uu___1041_6366 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1041_6366.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1041_6366.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1041_6366.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1041_6366.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1041_6366.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1041_6366.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1041_6366.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1041_6366.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1041_6366.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1041_6366.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1041_6366.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1041_6366.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1041_6366.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1041_6366.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___1041_6366.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1041_6366.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___1041_6366.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1041_6366.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___1041_6366.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1041_6366.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1041_6366.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1041_6366.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1041_6366.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1041_6366.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1041_6366.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1041_6366.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1041_6366.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1041_6366.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1041_6366.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1041_6366.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1041_6366.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1041_6366.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1041_6366.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1041_6366.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___1041_6366.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___1041_6366.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1041_6366.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1041_6366.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1041_6366.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1041_6366.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1041_6366.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1041_6366.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        let check_term lid univs1 t =
          let uu____6386 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____6386 with
          | (univs2,t1) ->
              ((let uu____6394 =
                  let uu____6396 =
                    let uu____6402 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____6402  in
                  FStar_All.pipe_left uu____6396
                    (FStar_Options.Other "Exports")
                   in
                if uu____6394
                then
                  let uu____6406 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____6408 =
                    let uu____6410 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____6410
                      (FStar_String.concat ", ")
                     in
                  let uu____6427 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____6406 uu____6408 uu____6427
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____6433 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____6433 (fun a1  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____6459 =
             let uu____6461 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____6463 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____6461 uu____6463
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____6459);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6474) ->
              let uu____6483 =
                let uu____6485 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6485  in
              if uu____6483
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____6499,uu____6500) ->
              let t =
                let uu____6512 =
                  let uu____6519 =
                    let uu____6520 =
                      let uu____6535 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____6535)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____6520  in
                  FStar_Syntax_Syntax.mk uu____6519  in
                uu____6512 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____6551,uu____6552,uu____6553) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____6563 =
                let uu____6565 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6565  in
              if uu____6563 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____6573,lbs),uu____6575) ->
              let uu____6586 =
                let uu____6588 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6588  in
              if uu____6586
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
              let uu____6611 =
                let uu____6613 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6613  in
              if uu____6611
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____6634 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____6635 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____6642 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____6643 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____6644 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____6645 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____6652 -> ()  in
        let uu____6653 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____6653 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____6759) -> true
             | uu____6761 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____6791 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____6830 ->
                   let uu____6831 =
                     let uu____6838 =
                       let uu____6839 =
                         let uu____6854 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____6854)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____6839  in
                     FStar_Syntax_Syntax.mk uu____6838  in
                   uu____6831 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____6871,uu____6872) ->
            let s1 =
              let uu___1167_6882 = s  in
              let uu____6883 =
                let uu____6884 =
                  let uu____6891 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____6891)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____6884  in
              let uu____6892 =
                let uu____6895 =
                  let uu____6898 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____6898  in
                FStar_Syntax_Syntax.Assumption :: uu____6895  in
              {
                FStar_Syntax_Syntax.sigel = uu____6883;
                FStar_Syntax_Syntax.sigrng =
                  (uu___1167_6882.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____6892;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___1167_6882.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___1167_6882.FStar_Syntax_Syntax.sigattrs);
                FStar_Syntax_Syntax.sigopts =
                  (uu___1167_6882.FStar_Syntax_Syntax.sigopts)
              }  in
            [s1]
        | uu____6901 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____6926 lbdef =
        match uu____6926 with
        | (uvs,t) ->
            let attrs =
              let uu____6937 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____6937
              then
                let uu____6942 =
                  let uu____6943 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____6943
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____6942 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___1180_6946 = s  in
            let uu____6947 =
              let uu____6950 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____6950  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___1180_6946.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____6947;
              FStar_Syntax_Syntax.sigmeta =
                (uu___1180_6946.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs;
              FStar_Syntax_Syntax.sigopts =
                (uu___1180_6946.FStar_Syntax_Syntax.sigopts)
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____6968 -> failwith "Impossible!"  in
        let c_opt =
          let uu____6975 = FStar_Syntax_Util.is_unit t  in
          if uu____6975
          then
            let uu____6982 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____6982
          else
            (let uu____6989 =
               let uu____6990 = FStar_Syntax_Subst.compress t  in
               uu____6990.FStar_Syntax_Syntax.n  in
             match uu____6989 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____6997,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____7021 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____7033 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____7033
            then false
            else
              (let uu____7040 = FStar_Syntax_Util.is_pure_or_ghost_comp c  in
               if uu____7040
               then true
               else
                 (let uu____7047 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____7047))
         in
      let extract_sigelt s =
        (let uu____7059 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____7059
         then
           let uu____7062 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____7062
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____7069 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____7089 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____7108 ->
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
                             (lid,uu____7154,uu____7155,uu____7156,uu____7157,uu____7158)
                             ->
                             ((let uu____7168 =
                                 let uu____7171 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____7171  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____7168);
                              (let uu____7220 = vals_of_abstract_inductive s1
                                  in
                               FStar_List.append uu____7220 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____7224,uu____7225,uu____7226,uu____7227,uu____7228)
                             ->
                             ((let uu____7236 =
                                 let uu____7239 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____7239  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____7236);
                              sigelts1)
                         | uu____7288 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____7297 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____7297
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____7307 =
                    let uu___1244_7308 = s  in
                    let uu____7309 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1244_7308.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1244_7308.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____7309;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1244_7308.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1244_7308.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1244_7308.FStar_Syntax_Syntax.sigopts)
                    }  in
                  [uu____7307])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____7320 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____7320
             then []
             else
               (let uu____7327 = lbs  in
                match uu____7327 with
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
                        (fun uu____7389  ->
                           match uu____7389 with
                           | (uu____7397,t,uu____7399) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____7416  ->
                             match uu____7416 with
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
                           (fun uu____7443  ->
                              match uu____7443 with
                              | (uu____7451,t,uu____7453) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____7465,uu____7466) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____7474 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____7503 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____7503) uu____7474
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____7507 =
                    let uu___1286_7508 = s  in
                    let uu____7509 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1286_7508.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1286_7508.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____7509;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1286_7508.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1286_7508.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1286_7508.FStar_Syntax_Syntax.sigopts)
                    }  in
                  [uu____7507]
                else [])
             else
               (let uu____7516 =
                  let uu___1288_7517 = s  in
                  let uu____7518 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1288_7517.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1288_7517.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____7518;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1288_7517.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1288_7517.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___1288_7517.FStar_Syntax_Syntax.sigopts)
                  }  in
                [uu____7516])
         | FStar_Syntax_Syntax.Sig_new_effect uu____7521 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7522 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____7523 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7524 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____7537 -> [s])
         in
      let uu___1300_7538 = m  in
      let uu____7539 =
        let uu____7540 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____7540 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___1300_7538.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____7539;
        FStar_Syntax_Syntax.exports =
          (uu___1300_7538.FStar_Syntax_Syntax.exports);
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
        (fun uu____7591  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____7638  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____7653 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____7653
  
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
      (let uu____7742 = FStar_Options.debug_any ()  in
       if uu____7742
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
         let uu___1325_7758 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___1325_7758.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___1325_7758.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___1325_7758.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___1325_7758.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___1325_7758.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___1325_7758.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___1325_7758.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___1325_7758.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___1325_7758.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___1325_7758.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___1325_7758.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___1325_7758.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___1325_7758.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___1325_7758.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___1325_7758.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___1325_7758.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___1325_7758.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___1325_7758.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___1325_7758.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___1325_7758.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___1325_7758.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___1325_7758.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___1325_7758.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___1325_7758.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___1325_7758.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___1325_7758.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___1325_7758.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___1325_7758.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___1325_7758.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___1325_7758.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___1325_7758.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___1325_7758.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___1325_7758.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___1325_7758.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___1325_7758.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___1325_7758.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___1325_7758.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___1325_7758.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___1325_7758.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___1325_7758.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___1325_7758.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___1325_7758.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___1325_7758.FStar_TypeChecker_Env.erasable_types_tab)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____7760 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____7760 with
       | (ses,exports,env3) ->
           ((let uu___1333_7793 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___1333_7793.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___1333_7793.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___1333_7793.FStar_Syntax_Syntax.is_interface)
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
        let uu____7822 = tc_decls env decls  in
        match uu____7822 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___1342_7853 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___1342_7853.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___1342_7853.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___1342_7853.FStar_Syntax_Syntax.is_interface)
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
        let uu____7914 = tc_partial_modul env01 m  in
        match uu____7914 with
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
                (let uu____7951 = FStar_Errors.get_err_count ()  in
                 uu____7951 = Prims.int_zero)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____7962 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____7962
                then
                  let uu____7966 =
                    let uu____7968 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____7968 then "" else " (in lax mode) "  in
                  let uu____7976 =
                    let uu____7978 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____7978
                    then
                      let uu____7982 =
                        let uu____7984 = FStar_Syntax_Print.modul_to_string m
                           in
                        Prims.op_Hat uu____7984 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____7982
                    else ""  in
                  let uu____7991 =
                    let uu____7993 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____7993
                    then
                      let uu____7997 =
                        let uu____7999 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____7999 "\n"  in
                      Prims.op_Hat "\nto: " uu____7997
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____7966
                    uu____7976 uu____7991
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___1368_8013 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1368_8013.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1368_8013.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1368_8013.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1368_8013.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1368_8013.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1368_8013.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1368_8013.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1368_8013.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1368_8013.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1368_8013.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1368_8013.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1368_8013.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1368_8013.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1368_8013.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1368_8013.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1368_8013.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1368_8013.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1368_8013.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1368_8013.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1368_8013.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1368_8013.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1368_8013.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1368_8013.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1368_8013.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1368_8013.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1368_8013.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1368_8013.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1368_8013.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1368_8013.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1368_8013.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1368_8013.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1368_8013.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1368_8013.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1368_8013.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1368_8013.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1368_8013.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1368_8013.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1368_8013.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1368_8013.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1368_8013.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1368_8013.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1368_8013.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1368_8013.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___1368_8013.FStar_TypeChecker_Env.erasable_types_tab)
                    }  in
                  let en02 =
                    let uu___1371_8015 = en01  in
                    let uu____8016 =
                      let uu____8031 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____8031, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1371_8015.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1371_8015.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1371_8015.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1371_8015.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1371_8015.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1371_8015.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1371_8015.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1371_8015.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1371_8015.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1371_8015.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1371_8015.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1371_8015.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1371_8015.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1371_8015.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1371_8015.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1371_8015.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1371_8015.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1371_8015.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1371_8015.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1371_8015.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1371_8015.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1371_8015.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1371_8015.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1371_8015.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1371_8015.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1371_8015.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1371_8015.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1371_8015.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1371_8015.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1371_8015.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____8016;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1371_8015.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1371_8015.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1371_8015.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1371_8015.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1371_8015.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1371_8015.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1371_8015.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1371_8015.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1371_8015.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1371_8015.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1371_8015.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1371_8015.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1371_8015.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___1371_8015.FStar_TypeChecker_Env.erasable_types_tab)
                    }  in
                  let uu____8077 =
                    let uu____8079 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____8079  in
                  if uu____8077
                  then
                    ((let uu____8083 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____8083 (fun a2  -> ()));
                     en02)
                  else en02  in
                let uu____8087 = tc_modul en0 modul_iface true  in
                match uu____8087 with
                | (modul_iface1,env) ->
                    ((let uu___1380_8100 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___1380_8100.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___1380_8100.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___1380_8100.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___1382_8104 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___1382_8104.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___1382_8104.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___1382_8104.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____8107 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____8107 FStar_Util.smap_clear);
               (let uu____8143 =
                  ((let uu____8147 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____8147) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____8150 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____8150)
                   in
                if uu____8143 then check_exports env modul exports else ());
               (let uu____8156 =
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____8156 (fun a3  -> ()));
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
        let uu____8171 =
          let uu____8173 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____8173  in
        push_context env uu____8171  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = add_sigelt_to_env env2 se true  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____8195 =
                         FStar_TypeChecker_Env.lookup_sigelt env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____8198 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____8198 with | (uu____8205,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____8230 = FStar_Options.debug_any ()  in
         if uu____8230
         then
           let uu____8233 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____8233
         else ());
        (let uu____8245 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____8245
         then
           let uu____8248 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____8248
         else ());
        (let env1 =
           let uu___1412_8254 = env  in
           let uu____8255 =
             let uu____8257 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____8257  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___1412_8254.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___1412_8254.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___1412_8254.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___1412_8254.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___1412_8254.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___1412_8254.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___1412_8254.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___1412_8254.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___1412_8254.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___1412_8254.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___1412_8254.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___1412_8254.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___1412_8254.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___1412_8254.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___1412_8254.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___1412_8254.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___1412_8254.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___1412_8254.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___1412_8254.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____8255;
             FStar_TypeChecker_Env.lax_universes =
               (uu___1412_8254.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___1412_8254.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___1412_8254.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___1412_8254.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___1412_8254.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___1412_8254.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___1412_8254.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___1412_8254.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___1412_8254.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___1412_8254.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___1412_8254.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___1412_8254.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___1412_8254.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___1412_8254.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___1412_8254.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___1412_8254.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___1412_8254.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___1412_8254.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___1412_8254.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___1412_8254.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___1412_8254.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___1412_8254.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___1412_8254.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___1412_8254.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___1412_8254.FStar_TypeChecker_Env.erasable_types_tab)
           }  in
         let uu____8259 = tc_modul env1 m b  in
         match uu____8259 with
         | (m1,env2) ->
             ((let uu____8271 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____8271
               then
                 let uu____8274 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____8274
               else ());
              (let uu____8280 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____8280
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
                         let uu____8318 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____8318 with
                         | (univnames1,e) ->
                             let uu___1434_8325 = lb  in
                             let uu____8326 =
                               let uu____8329 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____8329 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1434_8325.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1434_8325.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1434_8325.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1434_8325.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____8326;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1434_8325.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1434_8325.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___1436_8330 = se  in
                       let uu____8331 =
                         let uu____8332 =
                           let uu____8339 =
                             let uu____8340 = FStar_List.map update lbs  in
                             (b1, uu____8340)  in
                           (uu____8339, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____8332  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____8331;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1436_8330.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1436_8330.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1436_8330.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___1436_8330.FStar_Syntax_Syntax.sigattrs);
                         FStar_Syntax_Syntax.sigopts =
                           (uu___1436_8330.FStar_Syntax_Syntax.sigopts)
                       }
                   | uu____8348 -> se  in
                 let normalized_module =
                   let uu___1440_8350 = m1  in
                   let uu____8351 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___1440_8350.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____8351;
                     FStar_Syntax_Syntax.exports =
                       (uu___1440_8350.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___1440_8350.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____8352 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____8352
               else ());
              (m1, env2)))
  