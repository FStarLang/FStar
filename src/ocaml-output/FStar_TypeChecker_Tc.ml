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
              (uu___16_73.FStar_TypeChecker_Env.strict_args_tab)
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
              (uu___25_137.FStar_TypeChecker_Env.strict_args_tab)
          }
  
let (log : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____193 =
         let uu____195 = FStar_TypeChecker_Env.current_module env  in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____195  in
       Prims.op_Negation uu____193)
  
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____212 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____212 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____242 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____242
         then
           let uu____246 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____246
         else ());
        (let uu____251 = FStar_TypeChecker_TcTerm.tc_term env t  in
         match uu____251 with
         | (t',uu____259,uu____260) ->
             ((let uu____262 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____262
               then
                 let uu____266 = FStar_Syntax_Print.term_to_string t'  in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____266
               else ());
              t'))
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____287 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____287
  
let check_nogen :
  'Auu____297 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____297 Prims.list * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let t1 = tc_check_trivial_guard env t k  in
        let uu____320 =
          FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Env.Beta]
            env t1
           in
        ([], uu____320)
  
let (monad_signature :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax))
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail1 uu____356 =
          let uu____357 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____363 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____357 uu____363  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____407)::(wp,uu____409)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____438 -> fail1 ())
        | uu____439 -> fail1 ()
  
let (tc_eff_decl_new :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      (let uu____452 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "ED")
          in
       if uu____452
       then
         let uu____457 = FStar_Syntax_Print.eff_decl_to_string false ed  in
         FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____457
       else ());
      (let uu____463 =
         let uu____468 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____468 with
         | (ed_univs_subst,ed_univs) ->
             let bs =
               let uu____492 =
                 FStar_Syntax_Subst.subst_binders ed_univs_subst
                   ed.FStar_Syntax_Syntax.binders
                  in
               FStar_Syntax_Subst.open_binders uu____492  in
             let uu____493 =
               let uu____500 =
                 FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
               FStar_TypeChecker_TcTerm.tc_tparams uu____500 bs  in
             (match uu____493 with
              | (bs1,uu____506,uu____507) ->
                  let uu____508 =
                    let tmp_t =
                      let uu____518 =
                        let uu____521 =
                          FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                            (fun _526  -> FStar_Pervasives_Native.Some _526)
                           in
                        FStar_Syntax_Syntax.mk_Total'
                          FStar_Syntax_Syntax.t_unit uu____521
                         in
                      FStar_Syntax_Util.arrow bs1 uu____518  in
                    let uu____527 =
                      FStar_TypeChecker_Util.generalize_universes env0 tmp_t
                       in
                    match uu____527 with
                    | (us,tmp_t1) ->
                        let uu____544 =
                          let uu____545 =
                            let uu____546 =
                              FStar_All.pipe_right tmp_t1
                                FStar_Syntax_Util.arrow_formals
                               in
                            FStar_All.pipe_right uu____546
                              FStar_Pervasives_Native.fst
                             in
                          FStar_All.pipe_right uu____545
                            FStar_Syntax_Subst.close_binders
                           in
                        (us, uu____544)
                     in
                  (match uu____508 with
                   | (us,bs2) ->
                       (match ed_univs with
                        | [] -> (us, bs2)
                        | uu____615 ->
                            let uu____618 =
                              ((FStar_List.length ed_univs) =
                                 (FStar_List.length us))
                                &&
                                (FStar_List.forall2
                                   (fun u1  ->
                                      fun u2  ->
                                        let uu____625 =
                                          FStar_Syntax_Syntax.order_univ_name
                                            u1 u2
                                           in
                                        uu____625 = Prims.int_zero) ed_univs
                                   us)
                               in
                            if uu____618
                            then (us, bs2)
                            else
                              (let uu____636 =
                                 let uu____642 =
                                   let uu____644 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length ed_univs)
                                      in
                                   let uu____646 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length us)
                                      in
                                   FStar_Util.format3
                                     "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                     uu____644 uu____646
                                    in
                                 (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                   uu____642)
                                  in
                               FStar_Errors.raise_error uu____636
                                 FStar_Range.dummyRange))))
          in
       match uu____463 with
       | (us,bs) ->
           let ed1 =
             let uu___101_657 = ed  in
             {
               FStar_Syntax_Syntax.cattributes =
                 (uu___101_657.FStar_Syntax_Syntax.cattributes);
               FStar_Syntax_Syntax.mname =
                 (uu___101_657.FStar_Syntax_Syntax.mname);
               FStar_Syntax_Syntax.univs = us;
               FStar_Syntax_Syntax.binders = bs;
               FStar_Syntax_Syntax.signature =
                 (uu___101_657.FStar_Syntax_Syntax.signature);
               FStar_Syntax_Syntax.ret_wp =
                 (uu___101_657.FStar_Syntax_Syntax.ret_wp);
               FStar_Syntax_Syntax.bind_wp =
                 (uu___101_657.FStar_Syntax_Syntax.bind_wp);
               FStar_Syntax_Syntax.if_then_else =
                 (uu___101_657.FStar_Syntax_Syntax.if_then_else);
               FStar_Syntax_Syntax.ite_wp =
                 (uu___101_657.FStar_Syntax_Syntax.ite_wp);
               FStar_Syntax_Syntax.stronger =
                 (uu___101_657.FStar_Syntax_Syntax.stronger);
               FStar_Syntax_Syntax.close_wp =
                 (uu___101_657.FStar_Syntax_Syntax.close_wp);
               FStar_Syntax_Syntax.trivial =
                 (uu___101_657.FStar_Syntax_Syntax.trivial);
               FStar_Syntax_Syntax.repr =
                 (uu___101_657.FStar_Syntax_Syntax.repr);
               FStar_Syntax_Syntax.return_repr =
                 (uu___101_657.FStar_Syntax_Syntax.return_repr);
               FStar_Syntax_Syntax.bind_repr =
                 (uu___101_657.FStar_Syntax_Syntax.bind_repr);
               FStar_Syntax_Syntax.actions =
                 (uu___101_657.FStar_Syntax_Syntax.actions);
               FStar_Syntax_Syntax.eff_attrs =
                 (uu___101_657.FStar_Syntax_Syntax.eff_attrs)
             }  in
           let uu____658 = FStar_Syntax_Subst.univ_var_opening us  in
           (match uu____658 with
            | (ed_univs_subst,ed_univs) ->
                let uu____677 =
                  let uu____682 =
                    FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                  FStar_Syntax_Subst.open_binders' uu____682  in
                (match uu____677 with
                 | (ed_bs,ed_bs_subst) ->
                     let op uu____702 =
                       match uu____702 with
                       | (us1,t) ->
                           let t1 =
                             let uu____722 =
                               FStar_Syntax_Subst.shift_subst
                                 ((FStar_List.length ed_bs) +
                                    (FStar_List.length us1)) ed_univs_subst
                                in
                             FStar_Syntax_Subst.subst uu____722 t  in
                           let uu____731 =
                             let uu____732 =
                               FStar_Syntax_Subst.shift_subst
                                 (FStar_List.length us1) ed_bs_subst
                                in
                             FStar_Syntax_Subst.subst uu____732 t1  in
                           (us1, uu____731)
                        in
                     let ed2 =
                       let uu___115_738 = ed1  in
                       let uu____739 = op ed1.FStar_Syntax_Syntax.signature
                          in
                       let uu____740 = op ed1.FStar_Syntax_Syntax.ret_wp  in
                       let uu____741 = op ed1.FStar_Syntax_Syntax.bind_wp  in
                       let uu____742 =
                         op ed1.FStar_Syntax_Syntax.if_then_else  in
                       let uu____743 = op ed1.FStar_Syntax_Syntax.ite_wp  in
                       let uu____744 = op ed1.FStar_Syntax_Syntax.stronger
                          in
                       let uu____745 = op ed1.FStar_Syntax_Syntax.close_wp
                          in
                       let uu____746 = op ed1.FStar_Syntax_Syntax.trivial  in
                       let uu____747 = op ed1.FStar_Syntax_Syntax.repr  in
                       let uu____748 = op ed1.FStar_Syntax_Syntax.return_repr
                          in
                       let uu____749 = op ed1.FStar_Syntax_Syntax.bind_repr
                          in
                       let uu____750 =
                         FStar_List.map
                           (fun a  ->
                              let uu___118_758 = a  in
                              let uu____759 =
                                let uu____760 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_defn))
                                   in
                                FStar_Pervasives_Native.snd uu____760  in
                              let uu____771 =
                                let uu____772 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_defn))
                                   in
                                FStar_Pervasives_Native.snd uu____772  in
                              {
                                FStar_Syntax_Syntax.action_name =
                                  (uu___118_758.FStar_Syntax_Syntax.action_name);
                                FStar_Syntax_Syntax.action_unqualified_name =
                                  (uu___118_758.FStar_Syntax_Syntax.action_unqualified_name);
                                FStar_Syntax_Syntax.action_univs =
                                  (uu___118_758.FStar_Syntax_Syntax.action_univs);
                                FStar_Syntax_Syntax.action_params =
                                  (uu___118_758.FStar_Syntax_Syntax.action_params);
                                FStar_Syntax_Syntax.action_defn = uu____759;
                                FStar_Syntax_Syntax.action_typ = uu____771
                              }) ed1.FStar_Syntax_Syntax.actions
                          in
                       {
                         FStar_Syntax_Syntax.cattributes =
                           (uu___115_738.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.mname =
                           (uu___115_738.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.univs =
                           (uu___115_738.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___115_738.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature = uu____739;
                         FStar_Syntax_Syntax.ret_wp = uu____740;
                         FStar_Syntax_Syntax.bind_wp = uu____741;
                         FStar_Syntax_Syntax.if_then_else = uu____742;
                         FStar_Syntax_Syntax.ite_wp = uu____743;
                         FStar_Syntax_Syntax.stronger = uu____744;
                         FStar_Syntax_Syntax.close_wp = uu____745;
                         FStar_Syntax_Syntax.trivial = uu____746;
                         FStar_Syntax_Syntax.repr = uu____747;
                         FStar_Syntax_Syntax.return_repr = uu____748;
                         FStar_Syntax_Syntax.bind_repr = uu____749;
                         FStar_Syntax_Syntax.actions = uu____750;
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___115_738.FStar_Syntax_Syntax.eff_attrs)
                       }  in
                     ((let uu____784 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env0)
                           (FStar_Options.Other "ED")
                          in
                       if uu____784
                       then
                         let uu____789 =
                           FStar_Syntax_Print.eff_decl_to_string false ed2
                            in
                         FStar_Util.print1
                           "After typechecking binders eff_decl: \n\t%s\n"
                           uu____789
                       else ());
                      (let env =
                         let uu____796 =
                           FStar_TypeChecker_Env.push_univ_vars env0 ed_univs
                            in
                         FStar_TypeChecker_Env.push_binders uu____796 ed_bs
                          in
                       let check_and_gen' uu____820 k =
                         match uu____820 with
                         | (us1,t) ->
                             let uu____838 =
                               FStar_Syntax_Subst.open_univ_vars us1 t  in
                             (match uu____838 with
                              | (us2,t1) ->
                                  let t2 =
                                    let env1 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env us2
                                       in
                                    match k with
                                    | FStar_Pervasives_Native.Some k1 ->
                                        tc_check_trivial_guard env1 t1 k1
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____856 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env1 t1
                                           in
                                        (match uu____856 with
                                         | (t2,uu____864,g) ->
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env1 g;
                                              t2))
                                     in
                                  let uu____867 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env t2
                                     in
                                  (match uu____867 with
                                   | (g_us,t3) ->
                                       (match us2 with
                                        | [] -> (g_us, t3)
                                        | uu____898 ->
                                            let uu____899 =
                                              ((FStar_List.length us2) =
                                                 (FStar_List.length g_us))
                                                &&
                                                (FStar_List.forall2
                                                   (fun u1  ->
                                                      fun u2  ->
                                                        let uu____906 =
                                                          FStar_Syntax_Syntax.order_univ_name
                                                            u1 u2
                                                           in
                                                        uu____906 =
                                                          Prims.int_zero) us2
                                                   g_us)
                                               in
                                            if uu____899
                                            then (g_us, t3)
                                            else
                                              (let uu____925 =
                                                 let uu____931 =
                                                   let uu____933 =
                                                     FStar_Util.string_of_int
                                                       (FStar_List.length us2)
                                                      in
                                                   let uu____935 =
                                                     FStar_Util.string_of_int
                                                       (FStar_List.length
                                                          g_us)
                                                      in
                                                   FStar_Util.format3
                                                     "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                                     "" uu____933 uu____935
                                                    in
                                                 (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                   uu____931)
                                                  in
                                               FStar_Errors.raise_error
                                                 uu____925
                                                 FStar_Range.dummyRange))))
                          in
                       let signature =
                         check_and_gen' ed2.FStar_Syntax_Syntax.signature
                           FStar_Pervasives_Native.None
                          in
                       (let uu____958 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env0)
                            (FStar_Options.Other "ED")
                           in
                        if uu____958
                        then
                          let uu____963 =
                            FStar_Syntax_Print.tscheme_to_string signature
                             in
                          FStar_Util.print1 "Typechecked signature: %s\n"
                            uu____963
                        else ());
                       (let fresh_a_and_wp uu____979 =
                          let fail1 t =
                            let uu____992 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env ed2.FStar_Syntax_Syntax.mname t
                               in
                            FStar_Errors.raise_error uu____992
                              FStar_Range.dummyRange
                             in
                          let uu____1004 =
                            FStar_TypeChecker_Env.inst_tscheme signature  in
                          match uu____1004 with
                          | (uu____1015,signature1) ->
                              let uu____1017 =
                                let uu____1018 =
                                  FStar_Syntax_Subst.compress signature1  in
                                uu____1018.FStar_Syntax_Syntax.n  in
                              (match uu____1017 with
                               | FStar_Syntax_Syntax.Tm_arrow
                                   (bs1,uu____1028) ->
                                   let bs2 =
                                     FStar_Syntax_Subst.open_binders bs1  in
                                   (match bs2 with
                                    | (a,uu____1057)::(wp,uu____1059)::[] ->
                                        (a, (wp.FStar_Syntax_Syntax.sort))
                                    | uu____1088 -> fail1 signature1)
                               | uu____1089 -> fail1 signature1)
                           in
                        let log_combinator s ts =
                          let uu____1103 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "ED")
                             in
                          if uu____1103
                          then
                            let uu____1108 =
                              FStar_Syntax_Print.tscheme_to_string ts  in
                            FStar_Util.print2 "Typechecked %s = %s\n" s
                              uu____1108
                          else ()  in
                        let ret_wp =
                          let uu____1114 = fresh_a_and_wp ()  in
                          match uu____1114 with
                          | (a,wp_sort) ->
                              let k =
                                let uu____1130 =
                                  let uu____1139 =
                                    FStar_Syntax_Syntax.mk_binder a  in
                                  let uu____1146 =
                                    let uu____1155 =
                                      let uu____1162 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      FStar_Syntax_Syntax.null_binder
                                        uu____1162
                                       in
                                    [uu____1155]  in
                                  uu____1139 :: uu____1146  in
                                let uu____1181 =
                                  FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                FStar_Syntax_Util.arrow uu____1130 uu____1181
                                 in
                              check_and_gen' ed2.FStar_Syntax_Syntax.ret_wp
                                (FStar_Pervasives_Native.Some k)
                           in
                        log_combinator "ret_wp" ret_wp;
                        (let bind_wp =
                           let uu____1187 = fresh_a_and_wp ()  in
                           match uu____1187 with
                           | (a,wp_sort_a) ->
                               let uu____1200 = fresh_a_and_wp ()  in
                               (match uu____1200 with
                                | (b,wp_sort_b) ->
                                    let wp_sort_a_b =
                                      let uu____1216 =
                                        let uu____1225 =
                                          let uu____1232 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1232
                                           in
                                        [uu____1225]  in
                                      let uu____1245 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____1216
                                        uu____1245
                                       in
                                    let k =
                                      let uu____1251 =
                                        let uu____1260 =
                                          FStar_Syntax_Syntax.null_binder
                                            FStar_Syntax_Syntax.t_range
                                           in
                                        let uu____1267 =
                                          let uu____1276 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1283 =
                                            let uu____1292 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____1299 =
                                              let uu____1308 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              let uu____1315 =
                                                let uu____1324 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a_b
                                                   in
                                                [uu____1324]  in
                                              uu____1308 :: uu____1315  in
                                            uu____1292 :: uu____1299  in
                                          uu____1276 :: uu____1283  in
                                        uu____1260 :: uu____1267  in
                                      let uu____1367 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____1251
                                        uu____1367
                                       in
                                    check_and_gen'
                                      ed2.FStar_Syntax_Syntax.bind_wp
                                      (FStar_Pervasives_Native.Some k))
                            in
                         log_combinator "bind_wp" bind_wp;
                         (let if_then_else1 =
                            let uu____1373 = fresh_a_and_wp ()  in
                            match uu____1373 with
                            | (a,wp_sort_a) ->
                                let p =
                                  let uu____1387 =
                                    let uu____1390 =
                                      FStar_Ident.range_of_lid
                                        ed2.FStar_Syntax_Syntax.mname
                                       in
                                    FStar_Pervasives_Native.Some uu____1390
                                     in
                                  let uu____1391 =
                                    let uu____1392 =
                                      FStar_Syntax_Util.type_u ()  in
                                    FStar_All.pipe_right uu____1392
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_Syntax_Syntax.new_bv uu____1387
                                    uu____1391
                                   in
                                let k =
                                  let uu____1404 =
                                    let uu____1413 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____1420 =
                                      let uu____1429 =
                                        FStar_Syntax_Syntax.mk_binder p  in
                                      let uu____1436 =
                                        let uu____1445 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_sort_a
                                           in
                                        let uu____1452 =
                                          let uu____1461 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____1461]  in
                                        uu____1445 :: uu____1452  in
                                      uu____1429 :: uu____1436  in
                                    uu____1413 :: uu____1420  in
                                  let uu____1498 =
                                    FStar_Syntax_Syntax.mk_Total wp_sort_a
                                     in
                                  FStar_Syntax_Util.arrow uu____1404
                                    uu____1498
                                   in
                                check_and_gen'
                                  ed2.FStar_Syntax_Syntax.if_then_else
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "if_then_else" if_then_else1;
                          (let ite_wp =
                             let uu____1504 = fresh_a_and_wp ()  in
                             match uu____1504 with
                             | (a,wp_sort_a) ->
                                 let k =
                                   let uu____1520 =
                                     let uu____1529 =
                                       FStar_Syntax_Syntax.mk_binder a  in
                                     let uu____1536 =
                                       let uu____1545 =
                                         FStar_Syntax_Syntax.null_binder
                                           wp_sort_a
                                          in
                                       [uu____1545]  in
                                     uu____1529 :: uu____1536  in
                                   let uu____1570 =
                                     FStar_Syntax_Syntax.mk_Total wp_sort_a
                                      in
                                   FStar_Syntax_Util.arrow uu____1520
                                     uu____1570
                                    in
                                 check_and_gen'
                                   ed2.FStar_Syntax_Syntax.ite_wp
                                   (FStar_Pervasives_Native.Some k)
                              in
                           log_combinator "ite_wp" ite_wp;
                           (let stronger =
                              let uu____1576 = fresh_a_and_wp ()  in
                              match uu____1576 with
                              | (a,wp_sort_a) ->
                                  let uu____1589 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____1589 with
                                   | (t,uu____1595) ->
                                       let k =
                                         let uu____1599 =
                                           let uu____1608 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____1615 =
                                             let uu____1624 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____1631 =
                                               let uu____1640 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____1640]  in
                                             uu____1624 :: uu____1631  in
                                           uu____1608 :: uu____1615  in
                                         let uu____1671 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____1599
                                           uu____1671
                                          in
                                       check_and_gen'
                                         ed2.FStar_Syntax_Syntax.stronger
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let close_wp =
                               let uu____1677 = fresh_a_and_wp ()  in
                               match uu____1677 with
                               | (a,wp_sort_a) ->
                                   let b =
                                     let uu____1691 =
                                       let uu____1694 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____1694
                                        in
                                     let uu____1695 =
                                       let uu____1696 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____1696
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____1691
                                       uu____1695
                                      in
                                   let wp_sort_b_a =
                                     let uu____1708 =
                                       let uu____1717 =
                                         let uu____1724 =
                                           FStar_Syntax_Syntax.bv_to_name b
                                            in
                                         FStar_Syntax_Syntax.null_binder
                                           uu____1724
                                          in
                                       [uu____1717]  in
                                     let uu____1737 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____1708
                                       uu____1737
                                      in
                                   let k =
                                     let uu____1743 =
                                       let uu____1752 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____1759 =
                                         let uu____1768 =
                                           FStar_Syntax_Syntax.mk_binder b
                                            in
                                         let uu____1775 =
                                           let uu____1784 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_b_a
                                              in
                                           [uu____1784]  in
                                         uu____1768 :: uu____1775  in
                                       uu____1752 :: uu____1759  in
                                     let uu____1815 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____1743
                                       uu____1815
                                      in
                                   check_and_gen'
                                     ed2.FStar_Syntax_Syntax.close_wp
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "close_wp" close_wp;
                             (let trivial =
                                let uu____1821 = fresh_a_and_wp ()  in
                                match uu____1821 with
                                | (a,wp_sort_a) ->
                                    let uu____1834 =
                                      FStar_Syntax_Util.type_u ()  in
                                    (match uu____1834 with
                                     | (t,uu____1840) ->
                                         let k =
                                           let uu____1844 =
                                             let uu____1853 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____1860 =
                                               let uu____1869 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____1869]  in
                                             uu____1853 :: uu____1860  in
                                           let uu____1894 =
                                             FStar_Syntax_Syntax.mk_GTotal t
                                              in
                                           FStar_Syntax_Util.arrow uu____1844
                                             uu____1894
                                            in
                                         check_and_gen'
                                           ed2.FStar_Syntax_Syntax.trivial
                                           (FStar_Pervasives_Native.Some k))
                                 in
                              log_combinator "trivial" trivial; ed2))))))))))))
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      (let uu____1911 = tc_eff_decl_new env0 ed  in
       FStar_All.pipe_right uu____1911 (fun a1  -> ()));
      (let uu____1912 =
         FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs  in
       match uu____1912 with
       | (open_annotated_univs,annotated_univ_names) ->
           let open_univs n_binders t =
             let uu____1944 =
               FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
                in
             FStar_Syntax_Subst.subst uu____1944 t  in
           let open_univs_binders n_binders bs =
             let uu____1960 =
               FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
                in
             FStar_Syntax_Subst.subst_binders uu____1960 bs  in
           let n_effect_params =
             FStar_List.length ed.FStar_Syntax_Syntax.binders  in
           let uu____1970 =
             let uu____1977 =
               open_univs_binders Prims.int_zero
                 ed.FStar_Syntax_Syntax.binders
                in
             let uu____1979 =
               open_univs n_effect_params
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.signature)
                in
             FStar_Syntax_Subst.open_term' uu____1977 uu____1979  in
           (match uu____1970 with
            | (effect_params_un,signature_un,opening) ->
                let env =
                  FStar_TypeChecker_Env.push_univ_vars env0
                    annotated_univ_names
                   in
                let uu____1988 =
                  FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un
                   in
                (match uu____1988 with
                 | (effect_params,env1,uu____1997) ->
                     let uu____1998 =
                       FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                         signature_un
                        in
                     (match uu____1998 with
                      | (signature,uu____2004) ->
                          let ed1 =
                            let uu___258_2006 = ed  in
                            {
                              FStar_Syntax_Syntax.cattributes =
                                (uu___258_2006.FStar_Syntax_Syntax.cattributes);
                              FStar_Syntax_Syntax.mname =
                                (uu___258_2006.FStar_Syntax_Syntax.mname);
                              FStar_Syntax_Syntax.univs =
                                (uu___258_2006.FStar_Syntax_Syntax.univs);
                              FStar_Syntax_Syntax.binders = effect_params;
                              FStar_Syntax_Syntax.signature = ([], signature);
                              FStar_Syntax_Syntax.ret_wp =
                                (uu___258_2006.FStar_Syntax_Syntax.ret_wp);
                              FStar_Syntax_Syntax.bind_wp =
                                (uu___258_2006.FStar_Syntax_Syntax.bind_wp);
                              FStar_Syntax_Syntax.if_then_else =
                                (uu___258_2006.FStar_Syntax_Syntax.if_then_else);
                              FStar_Syntax_Syntax.ite_wp =
                                (uu___258_2006.FStar_Syntax_Syntax.ite_wp);
                              FStar_Syntax_Syntax.stronger =
                                (uu___258_2006.FStar_Syntax_Syntax.stronger);
                              FStar_Syntax_Syntax.close_wp =
                                (uu___258_2006.FStar_Syntax_Syntax.close_wp);
                              FStar_Syntax_Syntax.trivial =
                                (uu___258_2006.FStar_Syntax_Syntax.trivial);
                              FStar_Syntax_Syntax.repr =
                                (uu___258_2006.FStar_Syntax_Syntax.repr);
                              FStar_Syntax_Syntax.return_repr =
                                (uu___258_2006.FStar_Syntax_Syntax.return_repr);
                              FStar_Syntax_Syntax.bind_repr =
                                (uu___258_2006.FStar_Syntax_Syntax.bind_repr);
                              FStar_Syntax_Syntax.actions =
                                (uu___258_2006.FStar_Syntax_Syntax.actions);
                              FStar_Syntax_Syntax.eff_attrs =
                                (uu___258_2006.FStar_Syntax_Syntax.eff_attrs)
                            }  in
                          let ed2 =
                            match (effect_params, annotated_univ_names) with
                            | ([],[]) -> ed1
                            | uu____2038 ->
                                let op uu____2070 =
                                  match uu____2070 with
                                  | (us,t) ->
                                      let n_us = FStar_List.length us  in
                                      let uu____2090 =
                                        let uu____2091 =
                                          FStar_Syntax_Subst.shift_subst n_us
                                            opening
                                           in
                                        let uu____2094 = open_univs n_us t
                                           in
                                        FStar_Syntax_Subst.subst uu____2091
                                          uu____2094
                                         in
                                      (us, uu____2090)
                                   in
                                let uu___270_2097 = ed1  in
                                let uu____2098 =
                                  op ed1.FStar_Syntax_Syntax.ret_wp  in
                                let uu____2099 =
                                  op ed1.FStar_Syntax_Syntax.bind_wp  in
                                let uu____2100 =
                                  op ed1.FStar_Syntax_Syntax.if_then_else  in
                                let uu____2101 =
                                  op ed1.FStar_Syntax_Syntax.ite_wp  in
                                let uu____2102 =
                                  op ed1.FStar_Syntax_Syntax.stronger  in
                                let uu____2103 =
                                  op ed1.FStar_Syntax_Syntax.close_wp  in
                                let uu____2104 =
                                  op ed1.FStar_Syntax_Syntax.trivial  in
                                let uu____2105 =
                                  op ed1.FStar_Syntax_Syntax.repr  in
                                let uu____2106 =
                                  op ed1.FStar_Syntax_Syntax.return_repr  in
                                let uu____2107 =
                                  op ed1.FStar_Syntax_Syntax.bind_repr  in
                                let uu____2108 =
                                  FStar_List.map
                                    (fun a  ->
                                       let uu___273_2116 = a  in
                                       let uu____2117 =
                                         let uu____2118 =
                                           op
                                             ((a.FStar_Syntax_Syntax.action_univs),
                                               (a.FStar_Syntax_Syntax.action_defn))
                                            in
                                         FStar_Pervasives_Native.snd
                                           uu____2118
                                          in
                                       let uu____2129 =
                                         let uu____2130 =
                                           op
                                             ((a.FStar_Syntax_Syntax.action_univs),
                                               (a.FStar_Syntax_Syntax.action_typ))
                                            in
                                         FStar_Pervasives_Native.snd
                                           uu____2130
                                          in
                                       {
                                         FStar_Syntax_Syntax.action_name =
                                           (uu___273_2116.FStar_Syntax_Syntax.action_name);
                                         FStar_Syntax_Syntax.action_unqualified_name
                                           =
                                           (uu___273_2116.FStar_Syntax_Syntax.action_unqualified_name);
                                         FStar_Syntax_Syntax.action_univs =
                                           (uu___273_2116.FStar_Syntax_Syntax.action_univs);
                                         FStar_Syntax_Syntax.action_params =
                                           (uu___273_2116.FStar_Syntax_Syntax.action_params);
                                         FStar_Syntax_Syntax.action_defn =
                                           uu____2117;
                                         FStar_Syntax_Syntax.action_typ =
                                           uu____2129
                                       }) ed1.FStar_Syntax_Syntax.actions
                                   in
                                {
                                  FStar_Syntax_Syntax.cattributes =
                                    (uu___270_2097.FStar_Syntax_Syntax.cattributes);
                                  FStar_Syntax_Syntax.mname =
                                    (uu___270_2097.FStar_Syntax_Syntax.mname);
                                  FStar_Syntax_Syntax.univs =
                                    annotated_univ_names;
                                  FStar_Syntax_Syntax.binders =
                                    (uu___270_2097.FStar_Syntax_Syntax.binders);
                                  FStar_Syntax_Syntax.signature =
                                    (uu___270_2097.FStar_Syntax_Syntax.signature);
                                  FStar_Syntax_Syntax.ret_wp = uu____2098;
                                  FStar_Syntax_Syntax.bind_wp = uu____2099;
                                  FStar_Syntax_Syntax.if_then_else =
                                    uu____2100;
                                  FStar_Syntax_Syntax.ite_wp = uu____2101;
                                  FStar_Syntax_Syntax.stronger = uu____2102;
                                  FStar_Syntax_Syntax.close_wp = uu____2103;
                                  FStar_Syntax_Syntax.trivial = uu____2104;
                                  FStar_Syntax_Syntax.repr = uu____2105;
                                  FStar_Syntax_Syntax.return_repr =
                                    uu____2106;
                                  FStar_Syntax_Syntax.bind_repr = uu____2107;
                                  FStar_Syntax_Syntax.actions = uu____2108;
                                  FStar_Syntax_Syntax.eff_attrs =
                                    (uu___270_2097.FStar_Syntax_Syntax.eff_attrs)
                                }
                             in
                          let wp_with_fresh_result_type env2 mname signature1
                            =
                            let fail1 t =
                              let uu____2175 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env2 mname t
                                 in
                              let uu____2181 = FStar_Ident.range_of_lid mname
                                 in
                              FStar_Errors.raise_error uu____2175 uu____2181
                               in
                            let uu____2188 =
                              let uu____2189 =
                                FStar_Syntax_Subst.compress signature1  in
                              uu____2189.FStar_Syntax_Syntax.n  in
                            match uu____2188 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                let bs1 = FStar_Syntax_Subst.open_binders bs
                                   in
                                (match bs1 with
                                 | (a,uu____2228)::(wp,uu____2230)::[] ->
                                     (a, (wp.FStar_Syntax_Syntax.sort))
                                 | uu____2259 -> fail1 signature1)
                            | uu____2260 -> fail1 signature1  in
                          let uu____2261 =
                            wp_with_fresh_result_type env1
                              ed2.FStar_Syntax_Syntax.mname
                              (FStar_Pervasives_Native.snd
                                 ed2.FStar_Syntax_Syntax.signature)
                             in
                          (match uu____2261 with
                           | (a,wp_a) ->
                               let fresh_effect_signature uu____2289 =
                                 match annotated_univ_names with
                                 | [] ->
                                     let uu____2296 =
                                       FStar_TypeChecker_TcTerm.tc_trivial_guard
                                         env1 signature_un
                                        in
                                     (match uu____2296 with
                                      | (signature1,uu____2308) ->
                                          wp_with_fresh_result_type env1
                                            ed2.FStar_Syntax_Syntax.mname
                                            signature1)
                                 | uu____2309 ->
                                     let uu____2312 =
                                       let uu____2317 =
                                         let uu____2318 =
                                           FStar_Syntax_Subst.close_univ_vars
                                             annotated_univ_names signature
                                            in
                                         (annotated_univ_names, uu____2318)
                                          in
                                       FStar_TypeChecker_Env.inst_tscheme
                                         uu____2317
                                        in
                                     (match uu____2312 with
                                      | (uu____2331,signature1) ->
                                          wp_with_fresh_result_type env1
                                            ed2.FStar_Syntax_Syntax.mname
                                            signature1)
                                  in
                               let env2 =
                                 let uu____2334 =
                                   FStar_Syntax_Syntax.new_bv
                                     FStar_Pervasives_Native.None
                                     (FStar_Pervasives_Native.snd
                                        ed2.FStar_Syntax_Syntax.signature)
                                    in
                                 FStar_TypeChecker_Env.push_bv env1
                                   uu____2334
                                  in
                               ((let uu____2340 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env0)
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____2340
                                 then
                                   let uu____2345 =
                                     FStar_Syntax_Print.lid_to_string
                                       ed2.FStar_Syntax_Syntax.mname
                                      in
                                   let uu____2347 =
                                     FStar_Syntax_Print.binders_to_string " "
                                       ed2.FStar_Syntax_Syntax.binders
                                      in
                                   let uu____2350 =
                                     FStar_Syntax_Print.tscheme_to_string
                                       ed2.FStar_Syntax_Syntax.signature
                                      in
                                   let uu____2352 =
                                     let uu____2354 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____2354
                                      in
                                   let uu____2355 =
                                     FStar_Syntax_Print.term_to_string
                                       a.FStar_Syntax_Syntax.sort
                                      in
                                   FStar_Util.print5
                                     "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                     uu____2345 uu____2347 uu____2350
                                     uu____2352 uu____2355
                                 else ());
                                (let check_and_gen' env3 uu____2390 k =
                                   match uu____2390 with
                                   | (us,t) ->
                                       (match annotated_univ_names with
                                        | [] -> check_and_gen env3 t k
                                        | uu____2426::uu____2427 ->
                                            let uu____2430 =
                                              FStar_Syntax_Subst.subst_tscheme
                                                open_annotated_univs 
                                                (us, t)
                                               in
                                            (match uu____2430 with
                                             | (us1,t1) ->
                                                 let uu____2453 =
                                                   FStar_Syntax_Subst.open_univ_vars
                                                     us1 t1
                                                    in
                                                 (match uu____2453 with
                                                  | (us2,t2) ->
                                                      let uu____2468 =
                                                        let uu____2469 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env3 us2
                                                           in
                                                        tc_check_trivial_guard
                                                          uu____2469 t2 k
                                                         in
                                                      let uu____2470 =
                                                        FStar_Syntax_Subst.close_univ_vars
                                                          us2 t2
                                                         in
                                                      (us2, uu____2470))))
                                    in
                                 let return_wp =
                                   let expected_k =
                                     let uu____2489 =
                                       let uu____2498 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____2505 =
                                         let uu____2514 =
                                           let uu____2521 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____2521
                                            in
                                         [uu____2514]  in
                                       uu____2498 :: uu____2505  in
                                     let uu____2540 =
                                       FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                     FStar_Syntax_Util.arrow uu____2489
                                       uu____2540
                                      in
                                   check_and_gen' env2
                                     ed2.FStar_Syntax_Syntax.ret_wp
                                     expected_k
                                    in
                                 let bind_wp =
                                   let uu____2544 = fresh_effect_signature ()
                                      in
                                   match uu____2544 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____2560 =
                                           let uu____2569 =
                                             let uu____2576 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a
                                                in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____2576
                                              in
                                           [uu____2569]  in
                                         let uu____2589 =
                                           FStar_Syntax_Syntax.mk_Total wp_b
                                            in
                                         FStar_Syntax_Util.arrow uu____2560
                                           uu____2589
                                          in
                                       let expected_k =
                                         let uu____2595 =
                                           let uu____2604 =
                                             FStar_Syntax_Syntax.null_binder
                                               FStar_Syntax_Syntax.t_range
                                              in
                                           let uu____2611 =
                                             let uu____2620 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____2627 =
                                               let uu____2636 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   b
                                                  in
                                               let uu____2643 =
                                                 let uu____2652 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_a
                                                    in
                                                 let uu____2659 =
                                                   let uu____2668 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       a_wp_b
                                                      in
                                                   [uu____2668]  in
                                                 uu____2652 :: uu____2659  in
                                               uu____2636 :: uu____2643  in
                                             uu____2620 :: uu____2627  in
                                           uu____2604 :: uu____2611  in
                                         let uu____2711 =
                                           FStar_Syntax_Syntax.mk_Total wp_b
                                            in
                                         FStar_Syntax_Util.arrow uu____2595
                                           uu____2711
                                          in
                                       check_and_gen' env2
                                         ed2.FStar_Syntax_Syntax.bind_wp
                                         expected_k
                                    in
                                 let if_then_else1 =
                                   let p =
                                     let uu____2724 =
                                       let uu____2727 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____2727
                                        in
                                     let uu____2728 =
                                       let uu____2729 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____2729
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____2724
                                       uu____2728
                                      in
                                   let expected_k =
                                     let uu____2741 =
                                       let uu____2750 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____2757 =
                                         let uu____2766 =
                                           FStar_Syntax_Syntax.mk_binder p
                                            in
                                         let uu____2773 =
                                           let uu____2782 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a
                                              in
                                           let uu____2789 =
                                             let uu____2798 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a
                                                in
                                             [uu____2798]  in
                                           uu____2782 :: uu____2789  in
                                         uu____2766 :: uu____2773  in
                                       uu____2750 :: uu____2757  in
                                     let uu____2835 =
                                       FStar_Syntax_Syntax.mk_Total wp_a  in
                                     FStar_Syntax_Util.arrow uu____2741
                                       uu____2835
                                      in
                                   check_and_gen' env2
                                     ed2.FStar_Syntax_Syntax.if_then_else
                                     expected_k
                                    in
                                 let ite_wp =
                                   let expected_k =
                                     let uu____2850 =
                                       let uu____2859 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____2866 =
                                         let uu____2875 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a
                                            in
                                         [uu____2875]  in
                                       uu____2859 :: uu____2866  in
                                     let uu____2900 =
                                       FStar_Syntax_Syntax.mk_Total wp_a  in
                                     FStar_Syntax_Util.arrow uu____2850
                                       uu____2900
                                      in
                                   check_and_gen' env2
                                     ed2.FStar_Syntax_Syntax.ite_wp
                                     expected_k
                                    in
                                 let stronger =
                                   let uu____2904 =
                                     FStar_Syntax_Util.type_u ()  in
                                   match uu____2904 with
                                   | (t,uu____2910) ->
                                       let expected_k =
                                         let uu____2914 =
                                           let uu____2923 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____2930 =
                                             let uu____2939 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a
                                                in
                                             let uu____2946 =
                                               let uu____2955 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_a
                                                  in
                                               [uu____2955]  in
                                             uu____2939 :: uu____2946  in
                                           uu____2923 :: uu____2930  in
                                         let uu____2986 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____2914
                                           uu____2986
                                          in
                                       check_and_gen' env2
                                         ed2.FStar_Syntax_Syntax.stronger
                                         expected_k
                                    in
                                 let close_wp =
                                   let b =
                                     let uu____2999 =
                                       let uu____3002 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____3002
                                        in
                                     let uu____3003 =
                                       let uu____3004 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____3004
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____2999
                                       uu____3003
                                      in
                                   let b_wp_a =
                                     let uu____3016 =
                                       let uu____3025 =
                                         let uu____3032 =
                                           FStar_Syntax_Syntax.bv_to_name b
                                            in
                                         FStar_Syntax_Syntax.null_binder
                                           uu____3032
                                          in
                                       [uu____3025]  in
                                     let uu____3045 =
                                       FStar_Syntax_Syntax.mk_Total wp_a  in
                                     FStar_Syntax_Util.arrow uu____3016
                                       uu____3045
                                      in
                                   let expected_k =
                                     let uu____3051 =
                                       let uu____3060 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____3067 =
                                         let uu____3076 =
                                           FStar_Syntax_Syntax.mk_binder b
                                            in
                                         let uu____3083 =
                                           let uu____3092 =
                                             FStar_Syntax_Syntax.null_binder
                                               b_wp_a
                                              in
                                           [uu____3092]  in
                                         uu____3076 :: uu____3083  in
                                       uu____3060 :: uu____3067  in
                                     let uu____3123 =
                                       FStar_Syntax_Syntax.mk_Total wp_a  in
                                     FStar_Syntax_Util.arrow uu____3051
                                       uu____3123
                                      in
                                   check_and_gen' env2
                                     ed2.FStar_Syntax_Syntax.close_wp
                                     expected_k
                                    in
                                 let trivial_wp =
                                   let uu____3127 =
                                     FStar_Syntax_Util.type_u ()  in
                                   match uu____3127 with
                                   | (t,uu____3133) ->
                                       let expected_k =
                                         let uu____3137 =
                                           let uu____3146 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____3153 =
                                             let uu____3162 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a
                                                in
                                             [uu____3162]  in
                                           uu____3146 :: uu____3153  in
                                         let uu____3187 =
                                           FStar_Syntax_Syntax.mk_GTotal t
                                            in
                                         FStar_Syntax_Util.arrow uu____3137
                                           uu____3187
                                          in
                                       check_and_gen' env2
                                         ed2.FStar_Syntax_Syntax.trivial
                                         expected_k
                                    in
                                 let uu____3190 =
                                   let uu____3201 =
                                     let uu____3202 =
                                       FStar_Syntax_Subst.compress
                                         (FStar_Pervasives_Native.snd
                                            ed2.FStar_Syntax_Syntax.repr)
                                        in
                                     uu____3202.FStar_Syntax_Syntax.n  in
                                   match uu____3201 with
                                   | FStar_Syntax_Syntax.Tm_unknown  ->
                                       ((ed2.FStar_Syntax_Syntax.repr),
                                         (ed2.FStar_Syntax_Syntax.bind_repr),
                                         (ed2.FStar_Syntax_Syntax.return_repr),
                                         (ed2.FStar_Syntax_Syntax.actions))
                                   | uu____3221 ->
                                       let repr =
                                         let uu____3223 =
                                           FStar_Syntax_Util.type_u ()  in
                                         match uu____3223 with
                                         | (t,uu____3229) ->
                                             let expected_k =
                                               let uu____3233 =
                                                 let uu____3242 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     a
                                                    in
                                                 let uu____3249 =
                                                   let uu____3258 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       wp_a
                                                      in
                                                   [uu____3258]  in
                                                 uu____3242 :: uu____3249  in
                                               let uu____3283 =
                                                 FStar_Syntax_Syntax.mk_GTotal
                                                   t
                                                  in
                                               FStar_Syntax_Util.arrow
                                                 uu____3233 uu____3283
                                                in
                                             tc_check_trivial_guard env2
                                               (FStar_Pervasives_Native.snd
                                                  ed2.FStar_Syntax_Syntax.repr)
                                               expected_k
                                          in
                                       let mk_repr' t wp =
                                         let repr1 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.EraseUniverses;
                                             FStar_TypeChecker_Env.AllowUnboundUniverses]
                                             env2 repr
                                            in
                                         let uu____3304 =
                                           let uu____3311 =
                                             let uu____3312 =
                                               let uu____3329 =
                                                 let uu____3340 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     t
                                                    in
                                                 let uu____3349 =
                                                   let uu____3360 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp
                                                      in
                                                   [uu____3360]  in
                                                 uu____3340 :: uu____3349  in
                                               (repr1, uu____3329)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3312
                                              in
                                           FStar_Syntax_Syntax.mk uu____3311
                                            in
                                         uu____3304
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                          in
                                       let mk_repr a1 wp =
                                         let uu____3418 =
                                           FStar_Syntax_Syntax.bv_to_name a1
                                            in
                                         mk_repr' uu____3418 wp  in
                                       let destruct_repr t =
                                         let uu____3433 =
                                           let uu____3434 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____3434.FStar_Syntax_Syntax.n
                                            in
                                         match uu____3433 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____3445,(t1,uu____3447)::
                                              (wp,uu____3449)::[])
                                             -> (t1, wp)
                                         | uu____3508 ->
                                             failwith "Unexpected repr type"
                                          in
                                       let bind_repr =
                                         let r =
                                           let uu____3520 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               FStar_Parser_Const.range_0
                                               FStar_Syntax_Syntax.delta_constant
                                               FStar_Pervasives_Native.None
                                              in
                                           FStar_All.pipe_right uu____3520
                                             FStar_Syntax_Syntax.fv_to_tm
                                            in
                                         let uu____3521 =
                                           fresh_effect_signature ()  in
                                         match uu____3521 with
                                         | (b,wp_b) ->
                                             let a_wp_b =
                                               let uu____3537 =
                                                 let uu____3546 =
                                                   let uu____3553 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____3553
                                                    in
                                                 [uu____3546]  in
                                               let uu____3566 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   wp_b
                                                  in
                                               FStar_Syntax_Util.arrow
                                                 uu____3537 uu____3566
                                                in
                                             let wp_f =
                                               FStar_Syntax_Syntax.gen_bv
                                                 "wp_f"
                                                 FStar_Pervasives_Native.None
                                                 wp_a
                                                in
                                             let wp_g =
                                               FStar_Syntax_Syntax.gen_bv
                                                 "wp_g"
                                                 FStar_Pervasives_Native.None
                                                 a_wp_b
                                                in
                                             let x_a =
                                               let uu____3574 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   a
                                                  in
                                               FStar_Syntax_Syntax.gen_bv
                                                 "x_a"
                                                 FStar_Pervasives_Native.None
                                                 uu____3574
                                                in
                                             let wp_g_x =
                                               let uu____3579 =
                                                 let uu____3584 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     wp_g
                                                    in
                                                 let uu____3585 =
                                                   let uu____3586 =
                                                     let uu____3595 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         x_a
                                                        in
                                                     FStar_All.pipe_left
                                                       FStar_Syntax_Syntax.as_arg
                                                       uu____3595
                                                      in
                                                   [uu____3586]  in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   uu____3584 uu____3585
                                                  in
                                               uu____3579
                                                 FStar_Pervasives_Native.None
                                                 FStar_Range.dummyRange
                                                in
                                             let res =
                                               let wp =
                                                 let uu____3626 =
                                                   let uu____3631 =
                                                     let uu____3632 =
                                                       FStar_TypeChecker_Env.inst_tscheme
                                                         bind_wp
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3632
                                                       FStar_Pervasives_Native.snd
                                                      in
                                                   let uu____3641 =
                                                     let uu____3642 =
                                                       let uu____3645 =
                                                         let uu____3648 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             a
                                                            in
                                                         let uu____3649 =
                                                           let uu____3652 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           let uu____3653 =
                                                             let uu____3656 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp_f
                                                                in
                                                             let uu____3657 =
                                                               let uu____3660
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_g
                                                                  in
                                                               [uu____3660]
                                                                in
                                                             uu____3656 ::
                                                               uu____3657
                                                              in
                                                           uu____3652 ::
                                                             uu____3653
                                                            in
                                                         uu____3648 ::
                                                           uu____3649
                                                          in
                                                       r :: uu____3645  in
                                                     FStar_List.map
                                                       FStar_Syntax_Syntax.as_arg
                                                       uu____3642
                                                      in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     uu____3631 uu____3641
                                                    in
                                                 uu____3626
                                                   FStar_Pervasives_Native.None
                                                   FStar_Range.dummyRange
                                                  in
                                               mk_repr b wp  in
                                             let maybe_range_arg =
                                               let uu____3678 =
                                                 FStar_Util.for_some
                                                   (FStar_Syntax_Util.attr_eq
                                                      FStar_Syntax_Util.dm4f_bind_range_attr)
                                                   ed2.FStar_Syntax_Syntax.eff_attrs
                                                  in
                                               if uu____3678
                                               then
                                                 let uu____3689 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_range
                                                    in
                                                 let uu____3696 =
                                                   let uu____3705 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       FStar_Syntax_Syntax.t_range
                                                      in
                                                   [uu____3705]  in
                                                 uu____3689 :: uu____3696
                                               else []  in
                                             let expected_k =
                                               let uu____3741 =
                                                 let uu____3750 =
                                                   let uu____3759 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       a
                                                      in
                                                   let uu____3766 =
                                                     let uu____3775 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         b
                                                        in
                                                     [uu____3775]  in
                                                   uu____3759 :: uu____3766
                                                    in
                                                 let uu____3800 =
                                                   let uu____3809 =
                                                     let uu____3818 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         wp_f
                                                        in
                                                     let uu____3825 =
                                                       let uu____3834 =
                                                         let uu____3841 =
                                                           let uu____3842 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               wp_f
                                                              in
                                                           mk_repr a
                                                             uu____3842
                                                            in
                                                         FStar_Syntax_Syntax.null_binder
                                                           uu____3841
                                                          in
                                                       let uu____3843 =
                                                         let uu____3852 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             wp_g
                                                            in
                                                         let uu____3859 =
                                                           let uu____3868 =
                                                             let uu____3875 =
                                                               let uu____3876
                                                                 =
                                                                 let uu____3885
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_binder
                                                                    x_a
                                                                    in
                                                                 [uu____3885]
                                                                  in
                                                               let uu____3904
                                                                 =
                                                                 let uu____3907
                                                                   =
                                                                   mk_repr b
                                                                    wp_g_x
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Syntax.mk_Total
                                                                   uu____3907
                                                                  in
                                                               FStar_Syntax_Util.arrow
                                                                 uu____3876
                                                                 uu____3904
                                                                in
                                                             FStar_Syntax_Syntax.null_binder
                                                               uu____3875
                                                              in
                                                           [uu____3868]  in
                                                         uu____3852 ::
                                                           uu____3859
                                                          in
                                                       uu____3834 ::
                                                         uu____3843
                                                        in
                                                     uu____3818 :: uu____3825
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____3809
                                                    in
                                                 FStar_List.append uu____3750
                                                   uu____3800
                                                  in
                                               let uu____3952 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   res
                                                  in
                                               FStar_Syntax_Util.arrow
                                                 uu____3741 uu____3952
                                                in
                                             let uu____3955 =
                                               FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                 env2 expected_k
                                                in
                                             (match uu____3955 with
                                              | (expected_k1,uu____3963,uu____3964)
                                                  ->
                                                  let env3 =
                                                    FStar_TypeChecker_Env.set_range
                                                      env2
                                                      (FStar_Pervasives_Native.snd
                                                         ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                     in
                                                  let env4 =
                                                    let uu___402_3971 = env3
                                                       in
                                                    {
                                                      FStar_TypeChecker_Env.solver
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.solver);
                                                      FStar_TypeChecker_Env.range
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.range);
                                                      FStar_TypeChecker_Env.curmodule
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.curmodule);
                                                      FStar_TypeChecker_Env.gamma
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.gamma);
                                                      FStar_TypeChecker_Env.gamma_sig
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.gamma_sig);
                                                      FStar_TypeChecker_Env.gamma_cache
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.gamma_cache);
                                                      FStar_TypeChecker_Env.modules
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.modules);
                                                      FStar_TypeChecker_Env.expected_typ
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.expected_typ);
                                                      FStar_TypeChecker_Env.sigtab
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.sigtab);
                                                      FStar_TypeChecker_Env.attrtab
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.attrtab);
                                                      FStar_TypeChecker_Env.is_pattern
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.is_pattern);
                                                      FStar_TypeChecker_Env.instantiate_imp
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.instantiate_imp);
                                                      FStar_TypeChecker_Env.effects
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.effects);
                                                      FStar_TypeChecker_Env.generalize
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.generalize);
                                                      FStar_TypeChecker_Env.letrecs
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.letrecs);
                                                      FStar_TypeChecker_Env.top_level
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.top_level);
                                                      FStar_TypeChecker_Env.check_uvars
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.check_uvars);
                                                      FStar_TypeChecker_Env.use_eq
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.use_eq);
                                                      FStar_TypeChecker_Env.is_iface
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.is_iface);
                                                      FStar_TypeChecker_Env.admit
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.admit);
                                                      FStar_TypeChecker_Env.lax
                                                        = true;
                                                      FStar_TypeChecker_Env.lax_universes
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.lax_universes);
                                                      FStar_TypeChecker_Env.phase1
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.phase1);
                                                      FStar_TypeChecker_Env.failhard
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.failhard);
                                                      FStar_TypeChecker_Env.nosynth
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.nosynth);
                                                      FStar_TypeChecker_Env.uvar_subtyping
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.uvar_subtyping);
                                                      FStar_TypeChecker_Env.tc_term
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.tc_term);
                                                      FStar_TypeChecker_Env.type_of
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.type_of);
                                                      FStar_TypeChecker_Env.universe_of
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.universe_of);
                                                      FStar_TypeChecker_Env.check_type_of
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.check_type_of);
                                                      FStar_TypeChecker_Env.use_bv_sorts
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.use_bv_sorts);
                                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                      FStar_TypeChecker_Env.normalized_eff_names
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.normalized_eff_names);
                                                      FStar_TypeChecker_Env.fv_delta_depths
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.fv_delta_depths);
                                                      FStar_TypeChecker_Env.proof_ns
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.proof_ns);
                                                      FStar_TypeChecker_Env.synth_hook
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.synth_hook);
                                                      FStar_TypeChecker_Env.splice
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.splice);
                                                      FStar_TypeChecker_Env.postprocess
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.postprocess);
                                                      FStar_TypeChecker_Env.is_native_tactic
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.is_native_tactic);
                                                      FStar_TypeChecker_Env.identifier_info
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.identifier_info);
                                                      FStar_TypeChecker_Env.tc_hooks
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.tc_hooks);
                                                      FStar_TypeChecker_Env.dsenv
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.dsenv);
                                                      FStar_TypeChecker_Env.nbe
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.nbe);
                                                      FStar_TypeChecker_Env.strict_args_tab
                                                        =
                                                        (uu___402_3971.FStar_TypeChecker_Env.strict_args_tab)
                                                    }  in
                                                  let br =
                                                    check_and_gen' env4
                                                      ed2.FStar_Syntax_Syntax.bind_repr
                                                      expected_k1
                                                     in
                                                  br)
                                          in
                                       let return_repr =
                                         let x_a =
                                           let uu____3984 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x_a"
                                             FStar_Pervasives_Native.None
                                             uu____3984
                                            in
                                         let res =
                                           let wp =
                                             let uu____3992 =
                                               let uu____3997 =
                                                 let uu____3998 =
                                                   FStar_TypeChecker_Env.inst_tscheme
                                                     return_wp
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3998
                                                   FStar_Pervasives_Native.snd
                                                  in
                                               let uu____4007 =
                                                 let uu____4008 =
                                                   let uu____4011 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   let uu____4012 =
                                                     let uu____4015 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         x_a
                                                        in
                                                     [uu____4015]  in
                                                   uu____4011 :: uu____4012
                                                    in
                                                 FStar_List.map
                                                   FStar_Syntax_Syntax.as_arg
                                                   uu____4008
                                                  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____3997 uu____4007
                                                in
                                             uu____3992
                                               FStar_Pervasives_Native.None
                                               FStar_Range.dummyRange
                                              in
                                           mk_repr a wp  in
                                         let expected_k =
                                           let uu____4027 =
                                             let uu____4036 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____4043 =
                                               let uu____4052 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   x_a
                                                  in
                                               [uu____4052]  in
                                             uu____4036 :: uu____4043  in
                                           let uu____4077 =
                                             FStar_Syntax_Syntax.mk_Total res
                                              in
                                           FStar_Syntax_Util.arrow uu____4027
                                             uu____4077
                                            in
                                         let uu____4080 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k
                                            in
                                         match uu____4080 with
                                         | (expected_k1,uu____4088,uu____4089)
                                             ->
                                             let env3 =
                                               FStar_TypeChecker_Env.set_range
                                                 env2
                                                 (FStar_Pervasives_Native.snd
                                                    ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                in
                                             let uu____4095 =
                                               check_and_gen' env3
                                                 ed2.FStar_Syntax_Syntax.return_repr
                                                 expected_k1
                                                in
                                             (match uu____4095 with
                                              | (univs1,repr1) ->
                                                  (match univs1 with
                                                   | [] -> ([], repr1)
                                                   | uu____4118 ->
                                                       FStar_Errors.raise_error
                                                         (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                           "Unexpected universe-polymorphic return for effect")
                                                         repr1.FStar_Syntax_Syntax.pos))
                                          in
                                       let actions =
                                         let check_action act =
                                           let uu____4133 =
                                             if
                                               act.FStar_Syntax_Syntax.action_univs
                                                 = []
                                             then (env2, act)
                                             else
                                               (let uu____4147 =
                                                  FStar_Syntax_Subst.univ_var_opening
                                                    act.FStar_Syntax_Syntax.action_univs
                                                   in
                                                match uu____4147 with
                                                | (usubst,uvs) ->
                                                    let uu____4170 =
                                                      FStar_TypeChecker_Env.push_univ_vars
                                                        env2 uvs
                                                       in
                                                    let uu____4171 =
                                                      let uu___431_4172 = act
                                                         in
                                                      let uu____4173 =
                                                        FStar_Syntax_Subst.subst_binders
                                                          usubst
                                                          act.FStar_Syntax_Syntax.action_params
                                                         in
                                                      let uu____4174 =
                                                        FStar_Syntax_Subst.subst
                                                          usubst
                                                          act.FStar_Syntax_Syntax.action_defn
                                                         in
                                                      let uu____4175 =
                                                        FStar_Syntax_Subst.subst
                                                          usubst
                                                          act.FStar_Syntax_Syntax.action_typ
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          =
                                                          (uu___431_4172.FStar_Syntax_Syntax.action_name);
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          =
                                                          (uu___431_4172.FStar_Syntax_Syntax.action_unqualified_name);
                                                        FStar_Syntax_Syntax.action_univs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.action_params
                                                          = uu____4173;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____4174;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____4175
                                                      }  in
                                                    (uu____4170, uu____4171))
                                              in
                                           match uu____4133 with
                                           | (env3,act1) ->
                                               let act_typ =
                                                 let uu____4179 =
                                                   let uu____4180 =
                                                     FStar_Syntax_Subst.compress
                                                       act1.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   uu____4180.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____4179 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let c1 =
                                                       FStar_Syntax_Util.comp_to_comp_typ
                                                         c
                                                        in
                                                     let uu____4206 =
                                                       FStar_Ident.lid_equals
                                                         c1.FStar_Syntax_Syntax.effect_name
                                                         ed2.FStar_Syntax_Syntax.mname
                                                        in
                                                     if uu____4206
                                                     then
                                                       let uu____4209 =
                                                         let uu____4212 =
                                                           let uu____4213 =
                                                             let uu____4214 =
                                                               FStar_List.hd
                                                                 c1.FStar_Syntax_Syntax.effect_args
                                                                in
                                                             FStar_Pervasives_Native.fst
                                                               uu____4214
                                                              in
                                                           mk_repr'
                                                             c1.FStar_Syntax_Syntax.result_typ
                                                             uu____4213
                                                            in
                                                         FStar_Syntax_Syntax.mk_Total
                                                           uu____4212
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         bs uu____4209
                                                     else
                                                       act1.FStar_Syntax_Syntax.action_typ
                                                 | uu____4237 ->
                                                     act1.FStar_Syntax_Syntax.action_typ
                                                  in
                                               let uu____4238 =
                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                   env3 act_typ
                                                  in
                                               (match uu____4238 with
                                                | (act_typ1,uu____4246,g_t)
                                                    ->
                                                    let env' =
                                                      let uu___448_4249 =
                                                        FStar_TypeChecker_Env.set_expected_typ
                                                          env3 act_typ1
                                                         in
                                                      {
                                                        FStar_TypeChecker_Env.solver
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.solver);
                                                        FStar_TypeChecker_Env.range
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.range);
                                                        FStar_TypeChecker_Env.curmodule
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.curmodule);
                                                        FStar_TypeChecker_Env.gamma
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.gamma);
                                                        FStar_TypeChecker_Env.gamma_sig
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.gamma_sig);
                                                        FStar_TypeChecker_Env.gamma_cache
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.gamma_cache);
                                                        FStar_TypeChecker_Env.modules
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.modules);
                                                        FStar_TypeChecker_Env.expected_typ
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.expected_typ);
                                                        FStar_TypeChecker_Env.sigtab
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.sigtab);
                                                        FStar_TypeChecker_Env.attrtab
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.attrtab);
                                                        FStar_TypeChecker_Env.is_pattern
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.is_pattern);
                                                        FStar_TypeChecker_Env.instantiate_imp
                                                          = false;
                                                        FStar_TypeChecker_Env.effects
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.effects);
                                                        FStar_TypeChecker_Env.generalize
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.generalize);
                                                        FStar_TypeChecker_Env.letrecs
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.letrecs);
                                                        FStar_TypeChecker_Env.top_level
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.top_level);
                                                        FStar_TypeChecker_Env.check_uvars
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.check_uvars);
                                                        FStar_TypeChecker_Env.use_eq
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.use_eq);
                                                        FStar_TypeChecker_Env.is_iface
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.is_iface);
                                                        FStar_TypeChecker_Env.admit
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.admit);
                                                        FStar_TypeChecker_Env.lax
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.lax);
                                                        FStar_TypeChecker_Env.lax_universes
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.lax_universes);
                                                        FStar_TypeChecker_Env.phase1
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.phase1);
                                                        FStar_TypeChecker_Env.failhard
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.failhard);
                                                        FStar_TypeChecker_Env.nosynth
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.nosynth);
                                                        FStar_TypeChecker_Env.uvar_subtyping
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.uvar_subtyping);
                                                        FStar_TypeChecker_Env.tc_term
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.tc_term);
                                                        FStar_TypeChecker_Env.type_of
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.type_of);
                                                        FStar_TypeChecker_Env.universe_of
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.universe_of);
                                                        FStar_TypeChecker_Env.check_type_of
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.check_type_of);
                                                        FStar_TypeChecker_Env.use_bv_sorts
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.use_bv_sorts);
                                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                        FStar_TypeChecker_Env.normalized_eff_names
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.normalized_eff_names);
                                                        FStar_TypeChecker_Env.fv_delta_depths
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.fv_delta_depths);
                                                        FStar_TypeChecker_Env.proof_ns
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.proof_ns);
                                                        FStar_TypeChecker_Env.synth_hook
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.synth_hook);
                                                        FStar_TypeChecker_Env.splice
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.splice);
                                                        FStar_TypeChecker_Env.postprocess
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.postprocess);
                                                        FStar_TypeChecker_Env.is_native_tactic
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.is_native_tactic);
                                                        FStar_TypeChecker_Env.identifier_info
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.identifier_info);
                                                        FStar_TypeChecker_Env.tc_hooks
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.tc_hooks);
                                                        FStar_TypeChecker_Env.dsenv
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.dsenv);
                                                        FStar_TypeChecker_Env.nbe
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.nbe);
                                                        FStar_TypeChecker_Env.strict_args_tab
                                                          =
                                                          (uu___448_4249.FStar_TypeChecker_Env.strict_args_tab)
                                                      }  in
                                                    ((let uu____4252 =
                                                        FStar_TypeChecker_Env.debug
                                                          env3
                                                          (FStar_Options.Other
                                                             "ED")
                                                         in
                                                      if uu____4252
                                                      then
                                                        let uu____4256 =
                                                          FStar_Ident.text_of_lid
                                                            act1.FStar_Syntax_Syntax.action_name
                                                           in
                                                        let uu____4258 =
                                                          FStar_Syntax_Print.term_to_string
                                                            act1.FStar_Syntax_Syntax.action_defn
                                                           in
                                                        let uu____4260 =
                                                          FStar_Syntax_Print.term_to_string
                                                            act_typ1
                                                           in
                                                        FStar_Util.print3
                                                          "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                          uu____4256
                                                          uu____4258
                                                          uu____4260
                                                      else ());
                                                     (let uu____4265 =
                                                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                          env'
                                                          act1.FStar_Syntax_Syntax.action_defn
                                                         in
                                                      match uu____4265 with
                                                      | (act_defn,uu____4273,g_a)
                                                          ->
                                                          let act_defn1 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Env.UnfoldUntil
                                                                 FStar_Syntax_Syntax.delta_constant]
                                                              env3 act_defn
                                                             in
                                                          let act_typ2 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Env.UnfoldUntil
                                                                 FStar_Syntax_Syntax.delta_constant;
                                                              FStar_TypeChecker_Env.Eager_unfolding;
                                                              FStar_TypeChecker_Env.Beta]
                                                              env3 act_typ1
                                                             in
                                                          let uu____4277 =
                                                            let act_typ3 =
                                                              FStar_Syntax_Subst.compress
                                                                act_typ2
                                                               in
                                                            match act_typ3.FStar_Syntax_Syntax.n
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_arrow
                                                                (bs,c) ->
                                                                let uu____4313
                                                                  =
                                                                  FStar_Syntax_Subst.open_comp
                                                                    bs c
                                                                   in
                                                                (match uu____4313
                                                                 with
                                                                 | (bs1,uu____4325)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____4332
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____4332
                                                                     in
                                                                    let uu____4335
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____4335
                                                                    with
                                                                    | 
                                                                    (k1,uu____4349,g)
                                                                    ->
                                                                    (k1, g)))
                                                            | uu____4353 ->
                                                                let uu____4354
                                                                  =
                                                                  let uu____4360
                                                                    =
                                                                    let uu____4362
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____4364
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____4362
                                                                    uu____4364
                                                                     in
                                                                  (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____4360)
                                                                   in
                                                                FStar_Errors.raise_error
                                                                  uu____4354
                                                                  act_defn1.FStar_Syntax_Syntax.pos
                                                             in
                                                          (match uu____4277
                                                           with
                                                           | (expected_k,g_k)
                                                               ->
                                                               let g =
                                                                 FStar_TypeChecker_Rel.teq
                                                                   env3
                                                                   act_typ2
                                                                   expected_k
                                                                  in
                                                               ((let uu____4382
                                                                   =
                                                                   let uu____4383
                                                                    =
                                                                    let uu____4384
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____4384
                                                                     in
                                                                   FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____4383
                                                                    in
                                                                 FStar_TypeChecker_Rel.force_trivial_guard
                                                                   env3
                                                                   uu____4382);
                                                                (let act_typ3
                                                                   =
                                                                   let uu____4386
                                                                    =
                                                                    let uu____4387
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____4387.FStar_Syntax_Syntax.n
                                                                     in
                                                                   match uu____4386
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____4412
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____4412
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____4419
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____4419
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____4439
                                                                    =
                                                                    let uu____4440
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____4440]
                                                                     in
                                                                    let uu____4441
                                                                    =
                                                                    let uu____4452
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____4452]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____4439;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____4441;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____4477
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____4477))
                                                                   | 
                                                                   uu____4480
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                    in
                                                                 let uu____4482
                                                                   =
                                                                   if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                   then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env3
                                                                    act_defn1
                                                                   else
                                                                    (let uu____4504
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____4504))
                                                                    in
                                                                 match uu____4482
                                                                 with
                                                                 | (univs1,act_defn2)
                                                                    ->
                                                                    let act_typ4
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.Beta]
                                                                    env3
                                                                    act_typ3
                                                                     in
                                                                    let act_typ5
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    univs1
                                                                    act_typ4
                                                                     in
                                                                    let uu___498_4523
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___498_4523.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___498_4523.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___498_4523.FStar_Syntax_Syntax.action_params);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn2;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    act_typ5
                                                                    }))))))
                                            in
                                         FStar_All.pipe_right
                                           ed2.FStar_Syntax_Syntax.actions
                                           (FStar_List.map check_action)
                                          in
                                       (([], repr), bind_repr, return_repr,
                                         actions)
                                    in
                                 match uu____3190 with
                                 | (repr,bind_repr,return_repr,actions) ->
                                     let t0 =
                                       let uu____4545 =
                                         let uu____4548 =
                                           FStar_All.pipe_right
                                             ed2.FStar_Syntax_Syntax.signature
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____4548
                                           FStar_Syntax_Syntax.mk_Total
                                          in
                                       FStar_Syntax_Util.arrow
                                         ed2.FStar_Syntax_Syntax.binders
                                         uu____4545
                                        in
                                     let uu____4563 =
                                       let uu____4570 =
                                         FStar_TypeChecker_Util.generalize_universes
                                           env0 t0
                                          in
                                       match uu____4570 with
                                       | (gen_univs,t) ->
                                           (match annotated_univ_names with
                                            | [] -> (gen_univs, t)
                                            | uu____4595 ->
                                                let uu____4598 =
                                                  ((FStar_List.length
                                                      gen_univs)
                                                     =
                                                     (FStar_List.length
                                                        annotated_univ_names))
                                                    &&
                                                    (FStar_List.forall2
                                                       (fun u1  ->
                                                          fun u2  ->
                                                            let uu____4605 =
                                                              FStar_Syntax_Syntax.order_univ_name
                                                                u1 u2
                                                               in
                                                            uu____4605 =
                                                              Prims.int_zero)
                                                       gen_univs
                                                       annotated_univ_names)
                                                   in
                                                if uu____4598
                                                then (gen_univs, t)
                                                else
                                                  (let uu____4620 =
                                                     let uu____4626 =
                                                       let uu____4628 =
                                                         FStar_Util.string_of_int
                                                           (FStar_List.length
                                                              annotated_univ_names)
                                                          in
                                                       let uu____4630 =
                                                         FStar_Util.string_of_int
                                                           (FStar_List.length
                                                              gen_univs)
                                                          in
                                                       FStar_Util.format2
                                                         "Expected an effect definition with %s universes; but found %s"
                                                         uu____4628
                                                         uu____4630
                                                        in
                                                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                       uu____4626)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____4620
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                        in
                                     (match uu____4563 with
                                      | (univs1,t) ->
                                          let signature1 =
                                            let uu____4653 =
                                              let uu____4666 =
                                                let uu____4667 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____4667.FStar_Syntax_Syntax.n
                                                 in
                                              (effect_params, uu____4666)  in
                                            match uu____4653 with
                                            | ([],uu____4680) -> t
                                            | (uu____4695,FStar_Syntax_Syntax.Tm_arrow
                                               (uu____4696,c)) ->
                                                FStar_Syntax_Util.comp_result
                                                  c
                                            | uu____4734 ->
                                                failwith
                                                  "Impossible : t is an arrow"
                                             in
                                          let close1 n1 ts =
                                            let ts1 =
                                              let uu____4764 =
                                                FStar_Syntax_Subst.close_tscheme
                                                  effect_params ts
                                                 in
                                              FStar_Syntax_Subst.close_univ_vars_tscheme
                                                univs1 uu____4764
                                               in
                                            let m =
                                              FStar_List.length
                                                (FStar_Pervasives_Native.fst
                                                   ts1)
                                               in
                                            (let uu____4771 =
                                               ((n1 >= Prims.int_zero) &&
                                                  (let uu____4775 =
                                                     FStar_Syntax_Util.is_unknown
                                                       (FStar_Pervasives_Native.snd
                                                          ts1)
                                                      in
                                                   Prims.op_Negation
                                                     uu____4775))
                                                 && (m <> n1)
                                                in
                                             if uu____4771
                                             then
                                               let error =
                                                 if m < n1
                                                 then
                                                   "not universe-polymorphic enough"
                                                 else
                                                   "too universe-polymorphic"
                                                  in
                                               let err_msg =
                                                 let uu____4793 =
                                                   FStar_Util.string_of_int m
                                                    in
                                                 let uu____4795 =
                                                   FStar_Util.string_of_int
                                                     n1
                                                    in
                                                 let uu____4797 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     ts1
                                                    in
                                                 FStar_Util.format4
                                                   "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                   error uu____4793
                                                   uu____4795 uu____4797
                                                  in
                                               FStar_Errors.raise_error
                                                 (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                   err_msg)
                                                 (FStar_Pervasives_Native.snd
                                                    ts1).FStar_Syntax_Syntax.pos
                                             else ());
                                            ts1  in
                                          let close_action act =
                                            let uu____4813 =
                                              close1 (~- Prims.int_one)
                                                ((act.FStar_Syntax_Syntax.action_univs),
                                                  (act.FStar_Syntax_Syntax.action_defn))
                                               in
                                            match uu____4813 with
                                            | (univs2,defn) ->
                                                let uu____4829 =
                                                  close1 (~- Prims.int_one)
                                                    ((act.FStar_Syntax_Syntax.action_univs),
                                                      (act.FStar_Syntax_Syntax.action_typ))
                                                   in
                                                (match uu____4829 with
                                                 | (univs',typ) ->
                                                     let uu___548_4846 = act
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___548_4846.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___548_4846.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = univs2;
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___548_4846.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = defn;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = typ
                                                     })
                                             in
                                          let ed3 =
                                            let uu___551_4849 = ed2  in
                                            let uu____4850 =
                                              close1 Prims.int_zero return_wp
                                               in
                                            let uu____4852 =
                                              close1 Prims.int_one bind_wp
                                               in
                                            let uu____4854 =
                                              close1 Prims.int_zero
                                                if_then_else1
                                               in
                                            let uu____4856 =
                                              close1 Prims.int_zero ite_wp
                                               in
                                            let uu____4858 =
                                              close1 Prims.int_zero stronger
                                               in
                                            let uu____4860 =
                                              close1 Prims.int_one close_wp
                                               in
                                            let uu____4862 =
                                              close1 Prims.int_zero
                                                trivial_wp
                                               in
                                            let uu____4864 =
                                              close1 Prims.int_zero repr  in
                                            let uu____4866 =
                                              close1 Prims.int_zero
                                                return_repr
                                               in
                                            let uu____4868 =
                                              close1 Prims.int_one bind_repr
                                               in
                                            let uu____4870 =
                                              FStar_List.map close_action
                                                actions
                                               in
                                            {
                                              FStar_Syntax_Syntax.cattributes
                                                =
                                                (uu___551_4849.FStar_Syntax_Syntax.cattributes);
                                              FStar_Syntax_Syntax.mname =
                                                (uu___551_4849.FStar_Syntax_Syntax.mname);
                                              FStar_Syntax_Syntax.univs =
                                                univs1;
                                              FStar_Syntax_Syntax.binders =
                                                effect_params;
                                              FStar_Syntax_Syntax.signature =
                                                ([], signature1);
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____4850;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____4852;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____4854;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____4856;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____4858;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____4860;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____4862;
                                              FStar_Syntax_Syntax.repr =
                                                uu____4864;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____4866;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____4868;
                                              FStar_Syntax_Syntax.actions =
                                                uu____4870;
                                              FStar_Syntax_Syntax.eff_attrs =
                                                (uu___551_4849.FStar_Syntax_Syntax.eff_attrs)
                                            }  in
                                          ((let uu____4878 =
                                              (FStar_TypeChecker_Env.debug
                                                 env2 FStar_Options.Low)
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2)
                                                   (FStar_Options.Other "ED"))
                                               in
                                            if uu____4878
                                            then
                                              let uu____4883 =
                                                FStar_Syntax_Print.eff_decl_to_string
                                                  false ed3
                                                 in
                                              FStar_Util.print_string
                                                uu____4883
                                            else ());
                                           ed3)))))))))
  
let (cps_and_elaborate :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun ed  ->
      let uu____4909 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature)
         in
      match uu____4909 with
      | (effect_binders_un,signature_un) ->
          let uu____4930 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____4930 with
           | (effect_binders,env1,uu____4949) ->
               let uu____4950 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____4950 with
                | (signature,uu____4966) ->
                    let raise_error1 uu____4982 =
                      match uu____4982 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____5018  ->
                           match uu____5018 with
                           | (bv,qual) ->
                               let uu____5037 =
                                 let uu___576_5038 = bv  in
                                 let uu____5039 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___576_5038.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___576_5038.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____5039
                                 }  in
                               (uu____5037, qual)) effect_binders
                       in
                    let uu____5044 =
                      let uu____5051 =
                        let uu____5052 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____5052.FStar_Syntax_Syntax.n  in
                      match uu____5051 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____5062)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____5094 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____5044 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____5120 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____5120
                           then
                             let uu____5123 =
                               let uu____5126 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____5126  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____5123
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____5174 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____5174 with
                           | (t2,comp,uu____5187) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____5196 =
                           open_and_check env1 []
                             (FStar_Pervasives_Native.snd
                                ed.FStar_Syntax_Syntax.repr)
                            in
                         (match uu____5196 with
                          | (repr,_comp) ->
                              ((let uu____5224 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____5224
                                then
                                  let uu____5228 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____5228
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env1
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       env1 FStar_Range.dummyRange)
                                   in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr
                                   in
                                let uu____5235 =
                                  recheck_debug "*" env1 wp_type  in
                                let wp_a =
                                  let uu____5238 =
                                    let uu____5239 =
                                      let uu____5240 =
                                        let uu____5257 =
                                          let uu____5268 =
                                            let uu____5277 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____5280 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____5277, uu____5280)  in
                                          [uu____5268]  in
                                        (wp_type, uu____5257)  in
                                      FStar_Syntax_Syntax.Tm_app uu____5240
                                       in
                                    mk1 uu____5239  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta] env1
                                    uu____5238
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____5328 =
                                      let uu____5335 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____5335)  in
                                    let uu____5341 =
                                      let uu____5350 =
                                        let uu____5357 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____5357
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____5350]  in
                                    uu____5328 :: uu____5341  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let uu____5394 =
                                  recheck_debug
                                    "turned into the effect signature" env1
                                    effect_signature
                                   in
                                let sigelts = FStar_Util.mk_ref []  in
                                let mk_lid name =
                                  FStar_Syntax_Util.dm4f_lid ed name  in
                                let elaborate_and_star dmff_env1
                                  other_binders item =
                                  let env2 =
                                    FStar_TypeChecker_DMFF.get_env dmff_env1
                                     in
                                  let uu____5460 = item  in
                                  match uu____5460 with
                                  | (u_item,item1) ->
                                      let uu____5475 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____5475 with
                                       | (item2,item_comp) ->
                                           ((let uu____5491 =
                                               let uu____5493 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____5493
                                                in
                                             if uu____5491
                                             then
                                               let uu____5496 =
                                                 let uu____5502 =
                                                   let uu____5504 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____5506 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____5504 uu____5506
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____5502)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____5496
                                             else ());
                                            (let uu____5512 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____5512 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let uu____5530 =
                                                   recheck_debug "*" env2
                                                     item_wp
                                                    in
                                                 let uu____5532 =
                                                   recheck_debug "_" env2
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab))))
                                   in
                                let uu____5534 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____5534 with
                                | (dmff_env1,uu____5560,bind_wp,bind_elab) ->
                                    let uu____5563 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____5563 with
                                     | (dmff_env2,uu____5589,return_wp,return_elab)
                                         ->
                                         let rc_gtot =
                                           {
                                             FStar_Syntax_Syntax.residual_effect
                                               =
                                               FStar_Parser_Const.effect_GTot_lid;
                                             FStar_Syntax_Syntax.residual_typ
                                               = FStar_Pervasives_Native.None;
                                             FStar_Syntax_Syntax.residual_flags
                                               = []
                                           }  in
                                         let lift_from_pure_wp =
                                           let uu____5598 =
                                             let uu____5599 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____5599.FStar_Syntax_Syntax.n
                                              in
                                           match uu____5598 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____5657 =
                                                 let uu____5676 =
                                                   let uu____5681 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____5681
                                                    in
                                                 match uu____5676 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____5763 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____5657 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____5817 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____5817 [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____5840 =
                                                          let uu____5841 =
                                                            let uu____5858 =
                                                              let uu____5869
                                                                =
                                                                let uu____5878
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11)
                                                                   in
                                                                let uu____5883
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____5878,
                                                                  uu____5883)
                                                                 in
                                                              [uu____5869]
                                                               in
                                                            (wp_type,
                                                              uu____5858)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____5841
                                                           in
                                                        mk1 uu____5840  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Env.Beta]
                                                        env0 raw_wp_b1
                                                       in
                                                    let uu____5919 =
                                                      let uu____5928 =
                                                        let uu____5929 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____5929
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____5928
                                                       in
                                                    (match uu____5919 with
                                                     | (bs1,body2,what') ->
                                                         let fail1 uu____5952
                                                           =
                                                           let error_msg =
                                                             let uu____5955 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2
                                                                in
                                                             let uu____5957 =
                                                               match what'
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                    -> "None"
                                                               | FStar_Pervasives_Native.Some
                                                                   rc ->
                                                                   FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____5955
                                                               uu____5957
                                                              in
                                                           raise_error1
                                                             (FStar_Errors.Fatal_WrongBodyTypeForReturnWP,
                                                               error_msg)
                                                            in
                                                         ((match what' with
                                                           | FStar_Pervasives_Native.None
                                                                -> fail1 ()
                                                           | FStar_Pervasives_Native.Some
                                                               rc ->
                                                               ((let uu____5967
                                                                   =
                                                                   let uu____5969
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                   Prims.op_Negation
                                                                    uu____5969
                                                                    in
                                                                 if
                                                                   uu____5967
                                                                 then
                                                                   fail1 ()
                                                                 else ());
                                                                (let uu____5974
                                                                   =
                                                                   FStar_Util.map_opt
                                                                    rc.FStar_Syntax_Syntax.residual_typ
                                                                    (fun rt 
                                                                    ->
                                                                    let g_opt
                                                                    =
                                                                    FStar_TypeChecker_Rel.try_teq
                                                                    true env1
                                                                    rt
                                                                    FStar_Syntax_Util.ktype0
                                                                     in
                                                                    match g_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g' ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1 g'
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail1 ())
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____5974
                                                                   (fun a2 
                                                                    -> ()))));
                                                          (let wp =
                                                             let t2 =
                                                               (FStar_Pervasives_Native.fst
                                                                  b21).FStar_Syntax_Syntax.sort
                                                                in
                                                             let pure_wp_type
                                                               =
                                                               FStar_TypeChecker_DMFF.double_star
                                                                 t2
                                                                in
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp"
                                                               FStar_Pervasives_Native.None
                                                               pure_wp_type
                                                              in
                                                           let body3 =
                                                             let uu____6003 =
                                                               let uu____6008
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp
                                                                  in
                                                               let uu____6009
                                                                 =
                                                                 let uu____6010
                                                                   =
                                                                   let uu____6019
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                   (uu____6019,
                                                                    FStar_Pervasives_Native.None)
                                                                    in
                                                                 [uu____6010]
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____6008
                                                                 uu____6009
                                                                in
                                                             uu____6003
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange
                                                              in
                                                           let uu____6054 =
                                                             let uu____6055 =
                                                               let uu____6064
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp
                                                                  in
                                                               [uu____6064]
                                                                in
                                                             b11 ::
                                                               uu____6055
                                                              in
                                                           let uu____6089 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what
                                                              in
                                                           FStar_Syntax_Util.abs
                                                             uu____6054
                                                             uu____6089
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____6092 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let return_wp1 =
                                           let uu____6100 =
                                             let uu____6101 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____6101.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6100 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____6159 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____6159
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____6180 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let bind_wp1 =
                                           let uu____6188 =
                                             let uu____6189 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____6189.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6188 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_constant_at_level
                                                      Prims.int_one)
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let uu____6223 =
                                                 let uu____6224 =
                                                   let uu____6233 =
                                                     let uu____6240 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____6240
                                                      in
                                                   [uu____6233]  in
                                                 FStar_List.append uu____6224
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____6223 body what
                                           | uu____6259 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedBindShape,
                                                   "unexpected shape for bind")
                                            in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = Prims.int_zero
                                           then t
                                           else
                                             (let uu____6289 =
                                                let uu____6290 =
                                                  let uu____6291 =
                                                    let uu____6308 =
                                                      let uu____6319 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____6319
                                                       in
                                                    (t, uu____6308)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____6291
                                                   in
                                                mk1 uu____6290  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____6289)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____6377 = f a2  in
                                               [uu____6377]
                                           | x::xs ->
                                               let uu____6388 =
                                                 apply_last1 f xs  in
                                               x :: uu____6388
                                            in
                                         let register name item =
                                           let p =
                                             FStar_Ident.path_of_lid
                                               ed.FStar_Syntax_Syntax.mname
                                              in
                                           let p' =
                                             apply_last1
                                               (fun s  ->
                                                  Prims.op_Hat "__"
                                                    (Prims.op_Hat s
                                                       (Prims.op_Hat
                                                          "_eff_override_"
                                                          name))) p
                                              in
                                           let l' =
                                             FStar_Ident.lid_of_path p'
                                               FStar_Range.dummyRange
                                              in
                                           let uu____6422 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____6422 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____6452 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____6452
                                                 then
                                                   let uu____6455 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____6455
                                                 else ());
                                                (let uu____6460 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____6460))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____6469 =
                                                 let uu____6474 = mk_lid name
                                                    in
                                                 let uu____6475 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____6474 uu____6475
                                                  in
                                               (match uu____6469 with
                                                | (sigelt,fv) ->
                                                    ((let uu____6479 =
                                                        let uu____6482 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____6482
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____6479);
                                                     fv))
                                            in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp2 =
                                           register "return_wp" return_wp1
                                            in
                                         ((let uu____6536 =
                                             let uu____6539 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.PushOptions
                                                       (FStar_Pervasives_Native.Some
                                                          "--admit_smt_queries true")))
                                                in
                                             let uu____6542 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____6539 :: uu____6542  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____6536);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           (let uu____6594 =
                                              let uu____6597 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     FStar_Syntax_Syntax.PopOptions)
                                                 in
                                              let uu____6598 =
                                                FStar_ST.op_Bang sigelts  in
                                              uu____6597 :: uu____6598  in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____6594);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            (let uu____6650 =
                                               let uu____6653 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.PushOptions
                                                         (FStar_Pervasives_Native.Some
                                                            "--admit_smt_queries true")))
                                                  in
                                               let uu____6656 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____6653 :: uu____6656  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____6650);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             (let uu____6708 =
                                                let uu____6711 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       FStar_Syntax_Syntax.PopOptions)
                                                   in
                                                let uu____6712 =
                                                  FStar_ST.op_Bang sigelts
                                                   in
                                                uu____6711 :: uu____6712  in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____6708);
                                             (let uu____6761 =
                                                FStar_List.fold_left
                                                  (fun uu____6801  ->
                                                     fun action  ->
                                                       match uu____6801 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____6822 =
                                                             let uu____6829 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____6829
                                                               params_un
                                                              in
                                                           (match uu____6822
                                                            with
                                                            | (action_params,env',uu____6838)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____6864
                                                                     ->
                                                                    match uu____6864
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____6883
                                                                    =
                                                                    let uu___769_6884
                                                                    = bv  in
                                                                    let uu____6885
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___769_6884.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___769_6884.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____6885
                                                                    }  in
                                                                    (uu____6883,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____6891
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____6891
                                                                 with
                                                                 | (dmff_env4,action_t,action_wp,action_elab)
                                                                    ->
                                                                    let name
                                                                    =
                                                                    ((action.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText
                                                                     in
                                                                    let action_typ_with_wp
                                                                    =
                                                                    FStar_TypeChecker_DMFF.trans_F
                                                                    dmff_env'
                                                                    action_t
                                                                    action_wp
                                                                     in
                                                                    let action_params2
                                                                    =
                                                                    FStar_Syntax_Subst.close_binders
                                                                    action_params1
                                                                     in
                                                                    let action_elab1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_elab
                                                                     in
                                                                    let action_typ_with_wp1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_typ_with_wp
                                                                     in
                                                                    let action_elab2
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    action_params2
                                                                    action_elab1
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let action_typ_with_wp2
                                                                    =
                                                                    match action_params2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    action_typ_with_wp1
                                                                    | 
                                                                    uu____6930
                                                                    ->
                                                                    let uu____6931
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____6931
                                                                     in
                                                                    ((
                                                                    let uu____6935
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____6935
                                                                    then
                                                                    let uu____6940
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____6943
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____6946
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____6948
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____6940
                                                                    uu____6943
                                                                    uu____6946
                                                                    uu____6948
                                                                    else ());
                                                                    (let action_elab3
                                                                    =
                                                                    register
                                                                    (Prims.op_Hat
                                                                    name
                                                                    "_elab")
                                                                    action_elab2
                                                                     in
                                                                    let action_typ_with_wp3
                                                                    =
                                                                    register
                                                                    (Prims.op_Hat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____6957
                                                                    =
                                                                    let uu____6960
                                                                    =
                                                                    let uu___791_6961
                                                                    = action
                                                                     in
                                                                    let uu____6962
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____6963
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___791_6961.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___791_6961.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___791_6961.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____6962;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____6963
                                                                    }  in
                                                                    uu____6960
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____6957))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____6761 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions
                                                     in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a"
                                                        FStar_Pervasives_Native.None
                                                        wp_a
                                                       in
                                                    let binders =
                                                      let uu____7007 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____7014 =
                                                        let uu____7023 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____7023]  in
                                                      uu____7007 ::
                                                        uu____7014
                                                       in
                                                    let uu____7048 =
                                                      let uu____7051 =
                                                        let uu____7052 =
                                                          let uu____7053 =
                                                            let uu____7070 =
                                                              let uu____7081
                                                                =
                                                                let uu____7090
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____7093
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____7090,
                                                                  uu____7093)
                                                                 in
                                                              [uu____7081]
                                                               in
                                                            (repr,
                                                              uu____7070)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____7053
                                                           in
                                                        mk1 uu____7052  in
                                                      let uu____7129 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____7051
                                                        uu____7129
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____7048
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let uu____7130 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr2 =
                                                    register "repr" repr1  in
                                                  let uu____7134 =
                                                    let uu____7143 =
                                                      let uu____7144 =
                                                        let uu____7147 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____7147
                                                         in
                                                      uu____7144.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____7143 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____7161)
                                                        ->
                                                        let uu____7198 =
                                                          let uu____7219 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____7219
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____7287 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____7198
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____7352 =
                                                               let uu____7353
                                                                 =
                                                                 let uu____7356
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____7356
                                                                  in
                                                               uu____7353.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____7352
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____7389
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____7389
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____7404
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____7435
                                                                     ->
                                                                    match uu____7435
                                                                    with
                                                                    | 
                                                                    (bv,uu____7444)
                                                                    ->
                                                                    let uu____7449
                                                                    =
                                                                    let uu____7451
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____7451
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____7449
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____7404
                                                                    with
                                                                    | 
                                                                    (pre_args,post_args)
                                                                    ->
                                                                    let post
                                                                    =
                                                                    match post_args
                                                                    with
                                                                    | 
                                                                    post::[]
                                                                    -> post
                                                                    | 
                                                                    [] ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____7543
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____7543
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____7553
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____7564
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____7564
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____7574
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____7577
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____7574,
                                                                    uu____7577)))
                                                              | uu____7592 ->
                                                                  let uu____7593
                                                                    =
                                                                    let uu____7599
                                                                    =
                                                                    let uu____7601
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____7601
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____7599)
                                                                     in
                                                                  raise_error1
                                                                    uu____7593))
                                                    | uu____7613 ->
                                                        let uu____7614 =
                                                          let uu____7620 =
                                                            let uu____7622 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type
                                                               in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____7622
                                                             in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____7620)
                                                           in
                                                        raise_error1
                                                          uu____7614
                                                     in
                                                  (match uu____7134 with
                                                   | (pre,post) ->
                                                       ((let uu____7655 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____7658 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____7661 =
                                                           register "wp"
                                                             wp_type
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___847_7664
                                                             = ed  in
                                                           let uu____7665 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____7666 =
                                                             let uu____7667 =
                                                               FStar_Syntax_Subst.close
                                                                 effect_binders1
                                                                 effect_signature
                                                                in
                                                             ([], uu____7667)
                                                              in
                                                           let uu____7674 =
                                                             let uu____7675 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____7675)
                                                              in
                                                           let uu____7682 =
                                                             let uu____7683 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____7683)
                                                              in
                                                           let uu____7690 =
                                                             let uu____7691 =
                                                               apply_close
                                                                 repr2
                                                                in
                                                             ([], uu____7691)
                                                              in
                                                           let uu____7698 =
                                                             let uu____7699 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____7699)
                                                              in
                                                           let uu____7706 =
                                                             let uu____7707 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____7707)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___847_7664.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___847_7664.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___847_7664.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____7665;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____7666;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____7674;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____7682;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___847_7664.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___847_7664.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___847_7664.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___847_7664.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___847_7664.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____7690;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____7698;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____7706;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___847_7664.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____7714 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____7714
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____7732
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____7732
                                                               then
                                                                 let uu____7736
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____7736
                                                               else ());
                                                              (let lift_from_pure_opt
                                                                 =
                                                                 if
                                                                   (FStar_List.length
                                                                    effect_binders1)
                                                                    =
                                                                    Prims.int_zero
                                                                 then
                                                                   let lift_from_pure
                                                                    =
                                                                    let uu____7756
                                                                    =
                                                                    let uu____7759
                                                                    =
                                                                    let uu____7760
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____7760)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____7759
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____7756;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____7767
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____7767
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____7770
                                                                 =
                                                                 let uu____7773
                                                                   =
                                                                   let uu____7776
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____7776
                                                                    in
                                                                 FStar_List.append
                                                                   uu____7773
                                                                   sigelts'
                                                                  in
                                                               (uu____7770,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____7817 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____7817 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____7852 = FStar_List.hd ses  in
            uu____7852.FStar_Syntax_Syntax.sigrng  in
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
           | uu____7857 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____7863,[],t,uu____7865,uu____7866);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____7868;
               FStar_Syntax_Syntax.sigattrs = uu____7869;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____7871,_t_top,_lex_t_top,_7905,uu____7874);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____7876;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____7877;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____7879,_t_cons,_lex_t_cons,_7913,uu____7882);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____7884;
                 FStar_Syntax_Syntax.sigattrs = uu____7885;_}::[]
               when
               ((_7905 = Prims.int_zero) && (_7913 = Prims.int_zero)) &&
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
                 let uu____7938 =
                   let uu____7945 =
                     let uu____7946 =
                       let uu____7953 =
                         let uu____7956 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____7956
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____7953, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____7946  in
                   FStar_Syntax_Syntax.mk uu____7945  in
                 uu____7938 FStar_Pervasives_Native.None r1  in
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
                   let uu____7971 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7971
                    in
                 let hd1 =
                   let uu____7973 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7973
                    in
                 let tl1 =
                   let uu____7975 =
                     let uu____7976 =
                       let uu____7983 =
                         let uu____7984 =
                           let uu____7991 =
                             let uu____7994 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____7994
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____7991, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____7984  in
                       FStar_Syntax_Syntax.mk uu____7983  in
                     uu____7976 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7975
                    in
                 let res =
                   let uu____8000 =
                     let uu____8007 =
                       let uu____8008 =
                         let uu____8015 =
                           let uu____8018 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____8018
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____8015,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____8008  in
                     FStar_Syntax_Syntax.mk uu____8007  in
                   uu____8000 FStar_Pervasives_Native.None r2  in
                 let uu____8021 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____8021
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
               let uu____8060 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____8060;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____8065 ->
               let err_msg =
                 let uu____8070 =
                   let uu____8072 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____8072  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____8070
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
    fun uu____8097  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____8097 with
          | (uvs,t) ->
              let uu____8110 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____8110 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____8122 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____8122 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____8140 =
                        let uu____8143 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____8143
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____8140)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____8166 =
          let uu____8167 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____8167 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____8166 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____8192 =
          let uu____8193 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____8193 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____8192 r
  
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
          (let uu____8242 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____8242
           then
             let uu____8245 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____8245
           else ());
          (let uu____8250 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____8250 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____8281 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____8281 FStar_List.flatten  in
               ((let uu____8295 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____8298 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____8298)
                    in
                 if uu____8295
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
                           let uu____8314 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____8324,uu____8325,uu____8326,uu____8327,uu____8328)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____8337 -> failwith "Impossible!"  in
                           match uu____8314 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Inductive type "
                                      (Prims.op_Hat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____8356 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____8366,uu____8367,ty_lid,uu____8369,uu____8370)
                               -> (data_lid, ty_lid)
                           | uu____8377 -> failwith "Impossible"  in
                         match uu____8356 with
                         | (data_lid,ty_lid) ->
                             let uu____8385 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____8388 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____8388)
                                in
                             if uu____8385
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Exception "
                                      (Prims.op_Hat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____8402 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____8407,uu____8408,uu____8409,uu____8410,uu____8411)
                         -> lid
                     | uu____8420 -> failwith "Impossible"  in
                   FStar_List.existsb
                     (fun s  ->
                        s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                     FStar_TypeChecker_TcInductive.early_prims_inductives
                    in
                 let is_noeq =
                   FStar_List.existsb
                     (fun q  -> q = FStar_Syntax_Syntax.Noeq) quals
                    in
                 let res =
                   let uu____8438 =
                     (((FStar_List.length tcs) = Prims.int_zero) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____8438
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
          let pop1 uu____8513 =
            let uu____8514 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___1025_8524  ->
               match () with
               | () ->
                   let uu____8531 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____8531 (fun r  -> pop1 (); r)) ()
          with | uu___1024_8562 -> (pop1 (); FStar_Exn.raise uu___1024_8562)
  
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
      | uu____8878 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____8936 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____8936 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____8961 .
    'Auu____8961 FStar_Pervasives_Native.option -> 'Auu____8961 Prims.list
  =
  fun uu___0_8970  ->
    match uu___0_8970 with
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
            let uu____9050 = collect1 tl1  in
            (match uu____9050 with
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
        | ((e,n1)::uu____9288,[]) ->
            FStar_Pervasives_Native.Some (e, n1, Prims.int_zero)
        | ([],(e,n1)::uu____9344) ->
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
          let uu____9554 =
            let uu____9556 = FStar_Options.ide ()  in
            Prims.op_Negation uu____9556  in
          if uu____9554
          then
            let uu____9559 =
              let uu____9564 = FStar_TypeChecker_Env.dsenv env  in
              let uu____9565 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____9564 uu____9565  in
            (match uu____9559 with
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
                              let uu____9598 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____9599 =
                                let uu____9605 =
                                  let uu____9607 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____9609 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____9607 uu____9609
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____9605)
                                 in
                              FStar_Errors.log_issue uu____9598 uu____9599
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____9616 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____9617 =
                                   let uu____9623 =
                                     let uu____9625 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____9625
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____9623)
                                    in
                                 FStar_Errors.log_issue uu____9616 uu____9617)
                              else ())
                         else ())))
          else ()
      | uu____9635 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____9680 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____9708 ->
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
             let uu____9768 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____9768
             then
               let ses1 =
                 let uu____9776 =
                   let uu____9777 =
                     let uu____9778 =
                       tc_inductive
                         (let uu___1157_9787 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1157_9787.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1157_9787.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1157_9787.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1157_9787.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1157_9787.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1157_9787.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1157_9787.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1157_9787.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1157_9787.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1157_9787.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1157_9787.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1157_9787.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1157_9787.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1157_9787.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1157_9787.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1157_9787.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1157_9787.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1157_9787.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1157_9787.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1157_9787.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1157_9787.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___1157_9787.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1157_9787.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1157_9787.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1157_9787.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1157_9787.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1157_9787.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1157_9787.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1157_9787.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1157_9787.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1157_9787.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1157_9787.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1157_9787.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1157_9787.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1157_9787.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1157_9787.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1157_9787.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1157_9787.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1157_9787.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1157_9787.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1157_9787.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1157_9787.FStar_TypeChecker_Env.strict_args_tab)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____9778
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____9777
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____9776
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____9801 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____9801
                 then
                   let uu____9806 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1161_9810 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1161_9810.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1161_9810.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1161_9810.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1161_9810.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____9806
                 else ());
                ses1)
             else ses  in
           let uu____9820 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____9820 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___1168_9844 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1168_9844.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1168_9844.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1168_9844.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1168_9844.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____9856 = cps_and_elaborate env ne  in
           (match uu____9856 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___1182_9895 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1182_9895.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1182_9895.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1182_9895.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1182_9895.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___1185_9897 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1185_9897.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1185_9897.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1185_9897.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1185_9897.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses), env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 =
             let uu____9904 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env)
                in
             if uu____9904
             then
               let ne1 =
                 let uu____9908 =
                   let uu____9909 =
                     let uu____9910 =
                       tc_eff_decl
                         (let uu___1191_9913 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1191_9913.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1191_9913.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1191_9913.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1191_9913.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1191_9913.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1191_9913.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1191_9913.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1191_9913.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1191_9913.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1191_9913.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1191_9913.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1191_9913.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1191_9913.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1191_9913.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1191_9913.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1191_9913.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1191_9913.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1191_9913.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1191_9913.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1191_9913.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1191_9913.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___1191_9913.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1191_9913.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1191_9913.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1191_9913.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1191_9913.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1191_9913.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1191_9913.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1191_9913.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1191_9913.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1191_9913.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1191_9913.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1191_9913.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1191_9913.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1191_9913.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1191_9913.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1191_9913.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1191_9913.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1191_9913.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1191_9913.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1191_9913.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1191_9913.FStar_TypeChecker_Env.strict_args_tab)
                          }) ne
                        in
                     FStar_All.pipe_right uu____9910
                       (fun ne1  ->
                          let uu___1194_9919 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1194_9919.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1194_9919.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1194_9919.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1194_9919.FStar_Syntax_Syntax.sigattrs)
                          })
                      in
                   FStar_All.pipe_right uu____9909
                     (FStar_TypeChecker_Normalize.elim_uvars env)
                    in
                 FStar_All.pipe_right uu____9908
                   FStar_Syntax_Util.eff_decl_of_new_effect
                  in
               ((let uu____9921 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____9921
                 then
                   let uu____9926 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1198_9930 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1198_9930.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1198_9930.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1198_9930.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1198_9930.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Effect decl after phase 1: %s\n"
                     uu____9926
                 else ());
                ne1)
             else ne  in
           let ne2 = tc_eff_decl env ne1  in
           let se1 =
             let uu___1203_9938 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne2);
               FStar_Syntax_Syntax.sigrng =
                 (uu___1203_9938.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___1203_9938.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___1203_9938.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___1203_9938.FStar_Syntax_Syntax.sigattrs)
             }  in
           ([se1], [], env0)
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env
               sub1.FStar_Syntax_Syntax.source
              in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env
               sub1.FStar_Syntax_Syntax.target
              in
           let uu____9946 =
             let uu____9953 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9953
              in
           (match uu____9946 with
            | (a,wp_a_src) ->
                let uu____9970 =
                  let uu____9977 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____9977
                   in
                (match uu____9970 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____9995 =
                         let uu____9998 =
                           let uu____9999 =
                             let uu____10006 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____10006)  in
                           FStar_Syntax_Syntax.NT uu____9999  in
                         [uu____9998]  in
                       FStar_Syntax_Subst.subst uu____9995 wp_b_tgt  in
                     let expected_k =
                       let uu____10014 =
                         let uu____10023 = FStar_Syntax_Syntax.mk_binder a
                            in
                         let uu____10030 =
                           let uu____10039 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____10039]  in
                         uu____10023 :: uu____10030  in
                       let uu____10064 =
                         FStar_Syntax_Syntax.mk_Total wp_a_tgt  in
                       FStar_Syntax_Util.arrow uu____10014 uu____10064  in
                     let repr_type eff_name a1 wp =
                       (let uu____10086 =
                          let uu____10088 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name
                             in
                          Prims.op_Negation uu____10088  in
                        if uu____10086
                        then
                          let uu____10091 =
                            let uu____10097 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____10097)
                             in
                          let uu____10101 =
                            FStar_TypeChecker_Env.get_range env  in
                          FStar_Errors.raise_error uu____10091 uu____10101
                        else ());
                       (let uu____10104 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name
                           in
                        match uu____10104 with
                        | FStar_Pervasives_Native.None  ->
                            failwith
                              "internal error: reifiable effect has no decl?"
                        | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                            let repr =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [FStar_Syntax_Syntax.U_unknown] env ed
                                ed.FStar_Syntax_Syntax.repr
                               in
                            let uu____10137 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____10138 =
                              let uu____10145 =
                                let uu____10146 =
                                  let uu____10163 =
                                    let uu____10174 =
                                      FStar_Syntax_Syntax.as_arg a1  in
                                    let uu____10183 =
                                      let uu____10194 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____10194]  in
                                    uu____10174 :: uu____10183  in
                                  (repr, uu____10163)  in
                                FStar_Syntax_Syntax.Tm_app uu____10146  in
                              FStar_Syntax_Syntax.mk uu____10145  in
                            uu____10138 FStar_Pervasives_Native.None
                              uu____10137)
                        in
                     let uu____10239 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____10412 =
                             if (FStar_List.length uvs) > Prims.int_zero
                             then
                               let uu____10423 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____10423 with
                               | (usubst,uvs1) ->
                                   let uu____10446 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____10447 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____10446, uu____10447)
                             else (env, lift_wp)  in
                           (match uu____10412 with
                            | (env1,lift_wp1) ->
                                let lift_wp2 =
                                  if (FStar_List.length uvs) = Prims.int_zero
                                  then check_and_gen env1 lift_wp1 expected_k
                                  else
                                    (let lift_wp2 =
                                       tc_check_trivial_guard env1 lift_wp1
                                         expected_k
                                        in
                                     let uu____10497 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____10497))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____10568 =
                             if (FStar_List.length what) > Prims.int_zero
                             then
                               let uu____10583 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____10583 with
                               | (usubst,uvs) ->
                                   let uu____10608 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____10608)
                             else ([], lift)  in
                           (match uu____10568 with
                            | (uvs,lift1) ->
                                ((let uu____10644 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____10644
                                  then
                                    let uu____10648 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____10648
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____10654 =
                                    let uu____10661 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____10661 lift1
                                     in
                                  match uu____10654 with
                                  | (lift2,comp,uu____10686) ->
                                      let uu____10687 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____10687 with
                                       | (uu____10716,lift_wp,lift_elab) ->
                                           let lift_wp1 =
                                             recheck_debug "lift-wp" env
                                               lift_wp
                                              in
                                           let lift_elab1 =
                                             recheck_debug "lift-elab" env
                                               lift_elab
                                              in
                                           if
                                             (FStar_List.length uvs) =
                                               Prims.int_zero
                                           then
                                             let uu____10748 =
                                               let uu____10759 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10759
                                                in
                                             let uu____10776 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____10748, uu____10776)
                                           else
                                             (let uu____10805 =
                                                let uu____10816 =
                                                  let uu____10825 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____10825)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____10816
                                                 in
                                              let uu____10840 =
                                                let uu____10849 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____10849)  in
                                              (uu____10805, uu____10840))))))
                        in
                     (match uu____10239 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___1279_10923 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1279_10923.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1279_10923.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1279_10923.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1279_10923.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1279_10923.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1279_10923.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1279_10923.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1279_10923.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1279_10923.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1279_10923.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1279_10923.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1279_10923.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1279_10923.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1279_10923.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1279_10923.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1279_10923.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1279_10923.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1279_10923.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1279_10923.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1279_10923.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1279_10923.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1279_10923.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1279_10923.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1279_10923.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1279_10923.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1279_10923.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1279_10923.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1279_10923.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1279_10923.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1279_10923.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1279_10923.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1279_10923.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1279_10923.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1279_10923.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1279_10923.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1279_10923.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1279_10923.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1279_10923.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1279_10923.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1279_10923.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1279_10923.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1279_10923.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1279_10923.FStar_TypeChecker_Env.strict_args_tab)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____10980 =
                                  let uu____10985 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____10985 with
                                  | (usubst,uvs1) ->
                                      let uu____11008 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____11009 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____11008, uu____11009)
                                   in
                                (match uu____10980 with
                                 | (env2,lift2) ->
                                     let uu____11022 =
                                       let uu____11029 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____11029
                                        in
                                     (match uu____11022 with
                                      | (a1,wp_a_src1) ->
                                          let wp_a =
                                            FStar_Syntax_Syntax.new_bv
                                              FStar_Pervasives_Native.None
                                              wp_a_src1
                                             in
                                          let a_typ =
                                            FStar_Syntax_Syntax.bv_to_name a1
                                             in
                                          let wp_a_typ =
                                            FStar_Syntax_Syntax.bv_to_name
                                              wp_a
                                             in
                                          let repr_f =
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.source
                                              a_typ wp_a_typ
                                             in
                                          let repr_result =
                                            let lift_wp1 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Env.EraseUniverses;
                                                FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                env2
                                                (FStar_Pervasives_Native.snd
                                                   lift_wp)
                                               in
                                            let lift_wp_a =
                                              let uu____11063 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____11064 =
                                                let uu____11071 =
                                                  let uu____11072 =
                                                    let uu____11089 =
                                                      let uu____11100 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____11109 =
                                                        let uu____11120 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____11120]  in
                                                      uu____11100 ::
                                                        uu____11109
                                                       in
                                                    (lift_wp1, uu____11089)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____11072
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____11071
                                                 in
                                              uu____11064
                                                FStar_Pervasives_Native.None
                                                uu____11063
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____11168 =
                                              let uu____11177 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____11184 =
                                                let uu____11193 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____11200 =
                                                  let uu____11209 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____11209]  in
                                                uu____11193 :: uu____11200
                                                 in
                                              uu____11177 :: uu____11184  in
                                            let uu____11240 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____11168 uu____11240
                                             in
                                          let uu____11243 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____11243 with
                                           | (expected_k2,uu____11261,uu____11262)
                                               ->
                                               let lift3 =
                                                 if
                                                   (FStar_List.length uvs) =
                                                     Prims.int_zero
                                                 then
                                                   check_and_gen env2 lift2
                                                     expected_k2
                                                 else
                                                   (let lift3 =
                                                      tc_check_trivial_guard
                                                        env2 lift2
                                                        expected_k2
                                                       in
                                                    let uu____11286 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____11286))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____11302 =
                              let uu____11304 =
                                let uu____11306 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____11306
                                  FStar_List.length
                                 in
                              uu____11304 <> Prims.int_one  in
                            if uu____11302
                            then
                              let uu____11328 =
                                let uu____11334 =
                                  let uu____11336 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____11338 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____11340 =
                                    let uu____11342 =
                                      let uu____11344 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____11344
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____11342
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____11336 uu____11338 uu____11340
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____11334)
                                 in
                              FStar_Errors.raise_error uu____11328 r
                            else ());
                           (let uu____11371 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____11382 =
                                   let uu____11384 =
                                     let uu____11387 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____11387
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____11384
                                     FStar_List.length
                                    in
                                 uu____11382 <> Prims.int_one)
                               in
                            if uu____11371
                            then
                              let uu____11441 =
                                let uu____11447 =
                                  let uu____11449 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____11451 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____11453 =
                                    let uu____11455 =
                                      let uu____11457 =
                                        let uu____11460 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____11460
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____11457
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____11455
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____11449 uu____11451 uu____11453
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____11447)
                                 in
                              FStar_Errors.raise_error uu____11441 r
                            else ());
                           (let sub2 =
                              let uu___1316_11519 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___1316_11519.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___1316_11519.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___1319_11521 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___1319_11521.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___1319_11521.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___1319_11521.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___1319_11521.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let uu____11535 =
             if (FStar_List.length uvs) = Prims.int_zero
             then (env, uvs, tps, c)
             else
               (let uu____11563 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____11563 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____11594 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____11594 c  in
                    let uu____11603 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____11603, uvs1, tps1, c1))
              in
           (match uu____11535 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____11625 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____11625 with
                 | (tps2,c2) ->
                     let uu____11642 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____11642 with
                      | (tps3,env3,us) ->
                          let uu____11662 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____11662 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____11690)::uu____11691 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____11710 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____11718 =
                                   let uu____11720 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____11720  in
                                 if uu____11718
                                 then
                                   let uu____11723 =
                                     let uu____11729 =
                                       let uu____11731 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____11733 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____11731 uu____11733
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____11729)
                                      in
                                   FStar_Errors.raise_error uu____11723 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____11741 =
                                   let uu____11742 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____11742
                                    in
                                 match uu____11741 with
                                 | (uvs2,t) ->
                                     let uu____11773 =
                                       let uu____11778 =
                                         let uu____11791 =
                                           let uu____11792 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____11792.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____11791)  in
                                       match uu____11778 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____11807,c5)) -> ([], c5)
                                       | (uu____11849,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____11888 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____11773 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               Prims.int_one
                                           then
                                             (let uu____11922 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____11922 with
                                              | (uu____11927,t1) ->
                                                  let uu____11929 =
                                                    let uu____11935 =
                                                      let uu____11937 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____11939 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____11943 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____11937
                                                        uu____11939
                                                        uu____11943
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____11935)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____11929 r)
                                           else ();
                                           (let se1 =
                                              let uu___1389_11950 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___1389_11950.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___1389_11950.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___1389_11950.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___1389_11950.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____11957,uu____11958,uu____11959) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_11964  ->
                   match uu___1_11964 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____11967 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____11973,uu____11974) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_11983  ->
                   match uu___1_11983 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____11986 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____11997 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____11997
             then
               let uu____12000 =
                 let uu____12006 =
                   let uu____12008 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____12008
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____12006)
                  in
               FStar_Errors.raise_error uu____12000 r
             else ());
            (let uu____12014 =
               let uu____12023 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____12023
               then
                 let uu____12034 =
                   tc_declare_typ
                     (let uu___1413_12037 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1413_12037.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1413_12037.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1413_12037.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1413_12037.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1413_12037.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1413_12037.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1413_12037.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1413_12037.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1413_12037.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1413_12037.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1413_12037.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1413_12037.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1413_12037.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1413_12037.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1413_12037.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1413_12037.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1413_12037.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1413_12037.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1413_12037.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1413_12037.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1413_12037.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1413_12037.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1413_12037.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1413_12037.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1413_12037.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1413_12037.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1413_12037.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1413_12037.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1413_12037.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1413_12037.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1413_12037.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1413_12037.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1413_12037.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1413_12037.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1413_12037.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1413_12037.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1413_12037.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1413_12037.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1413_12037.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1413_12037.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___1413_12037.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___1413_12037.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1413_12037.FStar_TypeChecker_Env.strict_args_tab)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____12034 with
                 | (uvs1,t1) ->
                     ((let uu____12062 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____12062
                       then
                         let uu____12067 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____12069 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____12067 uu____12069
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____12014 with
             | (uvs1,t1) ->
                 let uu____12104 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____12104 with
                  | (uvs2,t2) ->
                      ([(let uu___1426_12134 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1426_12134.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1426_12134.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1426_12134.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1426_12134.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____12139 =
             let uu____12148 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____12148
             then
               let uu____12159 =
                 tc_assume
                   (let uu___1435_12162 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1435_12162.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1435_12162.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1435_12162.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1435_12162.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1435_12162.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1435_12162.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1435_12162.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1435_12162.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1435_12162.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1435_12162.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1435_12162.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1435_12162.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1435_12162.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1435_12162.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1435_12162.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1435_12162.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1435_12162.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1435_12162.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1435_12162.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1435_12162.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1435_12162.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___1435_12162.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1435_12162.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1435_12162.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1435_12162.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1435_12162.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1435_12162.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1435_12162.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1435_12162.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1435_12162.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1435_12162.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1435_12162.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1435_12162.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1435_12162.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1435_12162.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1435_12162.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1435_12162.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1435_12162.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1435_12162.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1435_12162.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1435_12162.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1435_12162.FStar_TypeChecker_Env.strict_args_tab)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____12159 with
               | (uvs1,t1) ->
                   ((let uu____12188 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____12188
                     then
                       let uu____12193 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12195 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____12193
                         uu____12195
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____12139 with
            | (uvs1,t1) ->
                let uu____12230 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____12230 with
                 | (uvs2,t2) ->
                     ([(let uu___1448_12260 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1448_12260.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1448_12260.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1448_12260.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1448_12260.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____12264 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____12264 with
            | (e1,c,g1) ->
                let uu____12284 =
                  let uu____12291 =
                    let uu____12294 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____12294  in
                  let uu____12295 =
                    let uu____12300 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____12300)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____12291 uu____12295
                   in
                (match uu____12284 with
                 | (e2,uu____12312,g) ->
                     ((let uu____12315 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____12315);
                      (let se1 =
                         let uu___1463_12317 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1463_12317.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1463_12317.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1463_12317.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1463_12317.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____12329 = FStar_Options.debug_any ()  in
             if uu____12329
             then
               let uu____12332 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____12334 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____12332
                 uu____12334
             else ());
            (let uu____12339 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____12339 with
             | (t1,uu____12357,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____12371 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____12371 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____12374 =
                              let uu____12380 =
                                let uu____12382 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____12384 =
                                  let uu____12386 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____12386
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____12382 uu____12384
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____12380)
                               in
                            FStar_Errors.raise_error uu____12374 r
                        | uu____12398 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___1484_12403 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1484_12403.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1484_12403.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1484_12403.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1484_12403.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1484_12403.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1484_12403.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1484_12403.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1484_12403.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1484_12403.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1484_12403.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1484_12403.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1484_12403.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1484_12403.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1484_12403.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1484_12403.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1484_12403.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1484_12403.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1484_12403.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1484_12403.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1484_12403.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___1484_12403.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1484_12403.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1484_12403.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1484_12403.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1484_12403.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1484_12403.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1484_12403.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1484_12403.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1484_12403.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1484_12403.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1484_12403.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1484_12403.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1484_12403.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1484_12403.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1484_12403.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1484_12403.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1484_12403.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1484_12403.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1484_12403.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1484_12403.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1484_12403.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___1484_12403.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1484_12403.FStar_TypeChecker_Env.strict_args_tab)
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
                 let uu____12471 =
                   let uu____12473 =
                     let uu____12482 = drop_logic val_q  in
                     let uu____12485 = drop_logic q'  in
                     (uu____12482, uu____12485)  in
                   match uu____12473 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____12471
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____12512 =
                      let uu____12518 =
                        let uu____12520 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____12522 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____12524 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____12520 uu____12522 uu____12524
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____12518)
                       in
                    FStar_Errors.raise_error uu____12512 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____12561 =
                   let uu____12562 = FStar_Syntax_Subst.compress def  in
                   uu____12562.FStar_Syntax_Syntax.n  in
                 match uu____12561 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____12574,uu____12575) -> binders
                 | uu____12600 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____12612;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____12717) -> val_bs1
                     | (uu____12748,[]) -> val_bs1
                     | ((body_bv,uu____12780)::bt,(val_bv,aqual)::vt) ->
                         let uu____12837 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____12861) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___1553_12875 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___1555_12878 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___1555_12878.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___1553_12875.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1553_12875.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____12837
                      in
                   let uu____12885 =
                     let uu____12892 =
                       let uu____12893 =
                         let uu____12908 = rename_binders1 def_bs val_bs  in
                         (uu____12908, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____12893  in
                     FStar_Syntax_Syntax.mk uu____12892  in
                   uu____12885 FStar_Pervasives_Native.None r1
               | uu____12927 -> typ1  in
             let uu___1561_12928 = lb  in
             let uu____12929 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___1561_12928.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1561_12928.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____12929;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1561_12928.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___1561_12928.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1561_12928.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1561_12928.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____12932 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____12987  ->
                     fun lb  ->
                       match uu____12987 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____13033 =
                             let uu____13045 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____13045 with
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
                                   | uu____13125 ->
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
                                  (let uu____13172 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____13172, quals_opt1)))
                              in
                           (match uu____13033 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____12932 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____13276 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___2_13282  ->
                                match uu___2_13282 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____13287 -> false))
                         in
                      if uu____13276
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____13300 =
                    let uu____13307 =
                      let uu____13308 =
                        let uu____13322 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____13322)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____13308  in
                    FStar_Syntax_Syntax.mk uu____13307  in
                  uu____13300 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___1604_13341 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1604_13341.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1604_13341.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1604_13341.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1604_13341.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1604_13341.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1604_13341.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1604_13341.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1604_13341.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1604_13341.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1604_13341.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1604_13341.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1604_13341.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1604_13341.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1604_13341.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1604_13341.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1604_13341.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1604_13341.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1604_13341.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1604_13341.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1604_13341.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1604_13341.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1604_13341.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1604_13341.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1604_13341.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1604_13341.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1604_13341.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1604_13341.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1604_13341.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1604_13341.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1604_13341.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1604_13341.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1604_13341.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1604_13341.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1604_13341.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1604_13341.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1604_13341.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1604_13341.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1604_13341.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1604_13341.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1604_13341.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1604_13341.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___1604_13341.FStar_TypeChecker_Env.strict_args_tab)
                  }  in
                let e1 =
                  let uu____13344 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____13344
                  then
                    let drop_lbtyp e_lax =
                      let uu____13353 =
                        let uu____13354 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____13354.FStar_Syntax_Syntax.n  in
                      match uu____13353 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____13376 =
                              let uu____13377 = FStar_Syntax_Subst.compress e
                                 in
                              uu____13377.FStar_Syntax_Syntax.n  in
                            match uu____13376 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____13381,lb1::[]),uu____13383) ->
                                let uu____13399 =
                                  let uu____13400 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____13400.FStar_Syntax_Syntax.n  in
                                (match uu____13399 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____13405 -> false)
                            | uu____13407 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___1629_13411 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___1631_13426 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___1631_13426.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___1631_13426.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___1631_13426.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___1631_13426.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___1631_13426.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___1631_13426.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___1629_13411.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___1629_13411.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____13429 -> e_lax  in
                    let uu____13430 =
                      FStar_Util.record_time
                        (fun uu____13438  ->
                           let uu____13439 =
                             let uu____13440 =
                               let uu____13441 =
                                 FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                   (let uu___1635_13450 = env'  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___1635_13450.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___1635_13450.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___1635_13450.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___1635_13450.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___1635_13450.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___1635_13450.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___1635_13450.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___1635_13450.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___1635_13450.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___1635_13450.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___1635_13450.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___1635_13450.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___1635_13450.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___1635_13450.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___1635_13450.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___1635_13450.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___1635_13450.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___1635_13450.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___1635_13450.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___1635_13450.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___1635_13450.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___1635_13450.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___1635_13450.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___1635_13450.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___1635_13450.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___1635_13450.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___1635_13450.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___1635_13450.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___1635_13450.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___1635_13450.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___1635_13450.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___1635_13450.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___1635_13450.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___1635_13450.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___1635_13450.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___1635_13450.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___1635_13450.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___1635_13450.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___1635_13450.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___1635_13450.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___1635_13450.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___1635_13450.FStar_TypeChecker_Env.strict_args_tab)
                                    }) e
                                  in
                               FStar_All.pipe_right uu____13441
                                 (fun uu____13463  ->
                                    match uu____13463 with
                                    | (e1,uu____13471,uu____13472) -> e1)
                                in
                             FStar_All.pipe_right uu____13440
                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                  env')
                              in
                           FStar_All.pipe_right uu____13439 drop_lbtyp)
                       in
                    match uu____13430 with
                    | (e1,ms) ->
                        ((let uu____13478 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TwoPhases")
                             in
                          if uu____13478
                          then
                            let uu____13483 =
                              FStar_Syntax_Print.term_to_string e1  in
                            FStar_Util.print1
                              "Let binding after phase 1: %s\n" uu____13483
                          else ());
                         (let uu____13489 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TCDeclTime")
                             in
                          if uu____13489
                          then
                            let uu____13494 = FStar_Util.string_of_int ms  in
                            FStar_Util.print1
                              "Let binding elaborated (phase 1) in %s milliseconds\n"
                              uu____13494
                          else ());
                         e1)
                  else e  in
                let uu____13501 =
                  let uu____13510 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____13510 with
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
                (match uu____13501 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___1665_13615 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___1665_13615.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1665_13615.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1665_13615.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1665_13615.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___1672_13628 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1672_13628.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1672_13628.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___1672_13628.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___1672_13628.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1672_13628.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1672_13628.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____13629 =
                       FStar_Util.record_time
                         (fun uu____13648  ->
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              env' e1)
                        in
                     (match uu____13629 with
                      | (r1,ms) ->
                          ((let uu____13676 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TCDeclTime")
                               in
                            if uu____13676
                            then
                              let uu____13681 = FStar_Util.string_of_int ms
                                 in
                              FStar_Util.print1
                                "Let binding typechecked in phase 2 in %s milliseconds\n"
                                uu____13681
                            else ());
                           (let uu____13686 =
                              match r1 with
                              | ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                                   FStar_Syntax_Syntax.pos = uu____13711;
                                   FStar_Syntax_Syntax.vars = uu____13712;_},uu____13713,g)
                                  when FStar_TypeChecker_Env.is_trivial g ->
                                  let lbs2 =
                                    let uu____13743 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.snd lbs1)
                                        (FStar_List.map rename_parameters)
                                       in
                                    ((FStar_Pervasives_Native.fst lbs1),
                                      uu____13743)
                                     in
                                  let lbs3 =
                                    let uu____13767 =
                                      match post_tau with
                                      | FStar_Pervasives_Native.Some tau ->
                                          FStar_List.map (postprocess_lb tau)
                                            (FStar_Pervasives_Native.snd lbs2)
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.snd lbs2
                                       in
                                    ((FStar_Pervasives_Native.fst lbs2),
                                      uu____13767)
                                     in
                                  let quals1 =
                                    match e2.FStar_Syntax_Syntax.n with
                                    | FStar_Syntax_Syntax.Tm_meta
                                        (uu____13790,FStar_Syntax_Syntax.Meta_desugared
                                         (FStar_Syntax_Syntax.Masked_effect
                                         ))
                                        ->
                                        FStar_Syntax_Syntax.HasMaskedEffect
                                        :: quals
                                    | uu____13795 -> quals  in
                                  ((let uu___1702_13804 = se1  in
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_let
                                           (lbs3, lids));
                                      FStar_Syntax_Syntax.sigrng =
                                        (uu___1702_13804.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals = quals1;
                                      FStar_Syntax_Syntax.sigmeta =
                                        (uu___1702_13804.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (uu___1702_13804.FStar_Syntax_Syntax.sigattrs)
                                    }), lbs3)
                              | uu____13807 ->
                                  failwith
                                    "impossible (typechecking should preserve Tm_let)"
                               in
                            match uu____13686 with
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
                                 (let uu____13863 = log env1  in
                                  if uu____13863
                                  then
                                    let uu____13866 =
                                      let uu____13868 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.snd lbs1)
                                          (FStar_List.map
                                             (fun lb  ->
                                                let should_log =
                                                  let uu____13888 =
                                                    let uu____13897 =
                                                      let uu____13898 =
                                                        let uu____13901 =
                                                          FStar_Util.right
                                                            lb.FStar_Syntax_Syntax.lbname
                                                           in
                                                        uu____13901.FStar_Syntax_Syntax.fv_name
                                                         in
                                                      uu____13898.FStar_Syntax_Syntax.v
                                                       in
                                                    FStar_TypeChecker_Env.try_lookup_val_decl
                                                      env1 uu____13897
                                                     in
                                                  match uu____13888 with
                                                  | FStar_Pervasives_Native.None
                                                       -> true
                                                  | uu____13910 -> false  in
                                                if should_log
                                                then
                                                  let uu____13922 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  let uu____13924 =
                                                    FStar_Syntax_Print.term_to_string
                                                      lb.FStar_Syntax_Syntax.lbtyp
                                                     in
                                                  FStar_Util.format2
                                                    "let %s : %s" uu____13922
                                                    uu____13924
                                                else ""))
                                         in
                                      FStar_All.pipe_right uu____13868
                                        (FStar_String.concat "\n")
                                       in
                                    FStar_Util.print1 "%s\n" uu____13866
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
      (let uu____13976 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____13976
       then
         let uu____13979 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____13979
       else ());
      (let uu____13984 = get_fail_se se  in
       match uu____13984 with
       | FStar_Pervasives_Native.Some (uu____14005,false ) when
           let uu____14022 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____14022 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___1733_14048 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___1733_14048.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___1733_14048.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___1733_14048.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___1733_14048.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___1733_14048.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___1733_14048.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___1733_14048.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___1733_14048.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___1733_14048.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___1733_14048.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___1733_14048.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___1733_14048.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___1733_14048.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___1733_14048.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___1733_14048.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___1733_14048.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___1733_14048.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___1733_14048.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___1733_14048.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___1733_14048.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___1733_14048.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___1733_14048.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___1733_14048.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___1733_14048.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___1733_14048.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___1733_14048.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___1733_14048.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___1733_14048.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___1733_14048.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___1733_14048.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___1733_14048.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___1733_14048.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___1733_14048.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___1733_14048.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___1733_14048.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___1733_14048.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___1733_14048.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___1733_14048.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___1733_14048.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___1733_14048.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___1733_14048.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___1733_14048.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___1733_14048.FStar_TypeChecker_Env.strict_args_tab)
               }
             else env1  in
           ((let uu____14053 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____14053
             then
               let uu____14056 =
                 let uu____14058 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____14058
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____14056
             else ());
            (let uu____14072 =
               FStar_Errors.catch_errors
                 (fun uu____14102  ->
                    FStar_Options.with_saved_options
                      (fun uu____14114  -> tc_decl' env' se))
                in
             match uu____14072 with
             | (errs,uu____14126) ->
                 ((let uu____14156 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____14156
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____14191 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____14191  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____14203 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____14214 =
                            let uu____14224 = check_multi_eq errnos1 actual
                               in
                            match uu____14224 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- Prims.int_one), (~- Prims.int_one),
                                  (~- Prims.int_one))
                             in
                          (match uu____14214 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____14289 =
                                   let uu____14295 =
                                     let uu____14297 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____14300 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____14303 =
                                       FStar_Util.string_of_int e  in
                                     let uu____14305 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____14307 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____14297 uu____14300 uu____14303
                                       uu____14305 uu____14307
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____14295)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____14289)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____14334 .
    'Auu____14334 ->
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
               (fun uu___3_14377  ->
                  match uu___3_14377 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____14380 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____14391) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____14399 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____14409 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____14414 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____14430 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____14456 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14482) ->
            let uu____14491 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____14491
            then
              let for_export_bundle se1 uu____14528 =
                match uu____14528 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____14567,uu____14568) ->
                         let dec =
                           let uu___1809_14578 = se1  in
                           let uu____14579 =
                             let uu____14580 =
                               let uu____14587 =
                                 let uu____14588 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____14588  in
                               (l, us, uu____14587)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____14580
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____14579;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1809_14578.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1809_14578.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1809_14578.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____14598,uu____14599,uu____14600) ->
                         let dec =
                           let uu___1820_14608 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1820_14608.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1820_14608.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1820_14608.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____14613 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____14636,uu____14637,uu____14638) ->
            let uu____14639 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____14639 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____14663 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____14663
            then
              ([(let uu___1836_14682 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___1836_14682.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___1836_14682.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___1836_14682.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____14685 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_14691  ->
                         match uu___4_14691 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____14694 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____14700 ->
                             true
                         | uu____14702 -> false))
                  in
               if uu____14685 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____14723 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____14728 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14733 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____14738 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14743 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____14761) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____14775 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____14775
            then ([], hidden)
            else
              (let dec =
                 let uu____14796 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____14796;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____14807 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____14807
            then
              let uu____14818 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1873_14832 = se  in
                        let uu____14833 =
                          let uu____14834 =
                            let uu____14841 =
                              let uu____14842 =
                                let uu____14845 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____14845.FStar_Syntax_Syntax.fv_name  in
                              uu____14842.FStar_Syntax_Syntax.v  in
                            (uu____14841, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____14834  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____14833;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1873_14832.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1873_14832.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1873_14832.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____14818, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____14868 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____14868
       then
         let uu____14871 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____14871
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____14876 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____14894 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
           uu____14911) ->
           let env1 =
             let uu___1894_14916 = env  in
             let uu____14917 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1894_14916.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1894_14916.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1894_14916.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1894_14916.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1894_14916.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1894_14916.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1894_14916.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1894_14916.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1894_14916.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1894_14916.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1894_14916.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1894_14916.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1894_14916.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1894_14916.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1894_14916.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1894_14916.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1894_14916.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1894_14916.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1894_14916.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1894_14916.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1894_14916.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1894_14916.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1894_14916.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1894_14916.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1894_14916.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1894_14916.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1894_14916.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1894_14916.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1894_14916.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1894_14916.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1894_14916.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1894_14916.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1894_14916.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1894_14916.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14917;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1894_14916.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1894_14916.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1894_14916.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1894_14916.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1894_14916.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1894_14916.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1894_14916.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1894_14916.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1894_14916.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
           let env1 =
             let uu___1894_14919 = env  in
             let uu____14920 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1894_14919.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1894_14919.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1894_14919.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1894_14919.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1894_14919.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1894_14919.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1894_14919.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1894_14919.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1894_14919.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1894_14919.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1894_14919.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1894_14919.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1894_14919.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1894_14919.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1894_14919.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1894_14919.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1894_14919.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1894_14919.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1894_14919.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1894_14919.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1894_14919.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1894_14919.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1894_14919.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1894_14919.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1894_14919.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1894_14919.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1894_14919.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1894_14919.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1894_14919.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1894_14919.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1894_14919.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1894_14919.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1894_14919.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1894_14919.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14920;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1894_14919.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1894_14919.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1894_14919.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1894_14919.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1894_14919.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1894_14919.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1894_14919.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1894_14919.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1894_14919.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions
           uu____14921) ->
           let env1 =
             let uu___1894_14924 = env  in
             let uu____14925 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1894_14924.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1894_14924.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1894_14924.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1894_14924.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1894_14924.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1894_14924.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1894_14924.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1894_14924.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1894_14924.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1894_14924.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1894_14924.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1894_14924.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1894_14924.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1894_14924.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1894_14924.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1894_14924.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1894_14924.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1894_14924.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1894_14924.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1894_14924.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1894_14924.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1894_14924.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1894_14924.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1894_14924.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1894_14924.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1894_14924.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1894_14924.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1894_14924.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1894_14924.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1894_14924.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1894_14924.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1894_14924.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1894_14924.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1894_14924.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14925;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1894_14924.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1894_14924.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1894_14924.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1894_14924.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1894_14924.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1894_14924.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1894_14924.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1894_14924.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1894_14924.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____14926) ->
           let env1 =
             let uu___1894_14931 = env  in
             let uu____14932 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1894_14931.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1894_14931.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1894_14931.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1894_14931.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1894_14931.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1894_14931.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1894_14931.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1894_14931.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1894_14931.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1894_14931.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1894_14931.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1894_14931.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1894_14931.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1894_14931.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1894_14931.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1894_14931.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1894_14931.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1894_14931.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1894_14931.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1894_14931.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1894_14931.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1894_14931.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1894_14931.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1894_14931.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1894_14931.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1894_14931.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1894_14931.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1894_14931.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1894_14931.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1894_14931.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1894_14931.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1894_14931.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1894_14931.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1894_14931.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14932;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1894_14931.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1894_14931.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1894_14931.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1894_14931.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1894_14931.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1894_14931.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1894_14931.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1894_14931.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1894_14931.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver )
           ->
           ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
              ();
            env)
       | FStar_Syntax_Syntax.Sig_pragma uu____14934 -> env
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14935 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____14945 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____14945) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____14946,uu____14947,uu____14948) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_14953  ->
                   match uu___5_14953 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____14956 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____14958,uu____14959) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_14968  ->
                   match uu___5_14968 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____14971 -> false))
           -> env
       | uu____14973 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____15042 se =
        match uu____15042 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____15095 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____15095
              then
                let uu____15098 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____15098
              else ());
             (let uu____15103 = tc_decl env1 se  in
              match uu____15103 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____15156 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____15156
                             then
                               let uu____15160 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____15160
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____15176 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____15176
                             then
                               let uu____15180 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____15180
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
                              fun se1  -> add_sigelt_to_env env3 se1) env2)
                       in
                    FStar_Syntax_Unionfind.reset ();
                    (let uu____15197 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____15197
                     then
                       let uu____15202 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____15211 =
                                  let uu____15213 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____15213 "\n"  in
                                Prims.op_Hat s uu____15211) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____15202
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____15223 =
                       let uu____15232 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____15232
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____15274 se1 =
                            match uu____15274 with
                            | (exports1,hidden1) ->
                                let uu____15302 = for_export env3 hidden1 se1
                                   in
                                (match uu____15302 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____15223 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____15456 = acc  in
        match uu____15456 with
        | (uu____15491,uu____15492,env1,uu____15494) ->
            let uu____15507 =
              FStar_Util.record_time
                (fun uu____15554  -> process_one_decl acc se)
               in
            (match uu____15507 with
             | (r,ms_elapsed) ->
                 ((let uu____15620 =
                     ((FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TCDeclTime"))
                        ||
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.attr_eq
                              FStar_Syntax_Util.tcdecltime_attr)
                           se.FStar_Syntax_Syntax.sigattrs))
                       || (FStar_Options.timing ())
                      in
                   if uu____15620
                   then
                     let uu____15624 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____15626 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____15624 uu____15626
                   else ());
                  r))
         in
      let uu____15631 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____15631 with
      | (ses1,exports,env1,uu____15679) ->
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
          let uu___1991_15717 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1991_15717.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1991_15717.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1991_15717.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1991_15717.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1991_15717.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1991_15717.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1991_15717.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1991_15717.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1991_15717.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1991_15717.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___1991_15717.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1991_15717.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1991_15717.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1991_15717.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1991_15717.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___1991_15717.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1991_15717.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___1991_15717.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1991_15717.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___1991_15717.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1991_15717.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1991_15717.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1991_15717.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1991_15717.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1991_15717.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1991_15717.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1991_15717.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1991_15717.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1991_15717.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1991_15717.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1991_15717.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1991_15717.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1991_15717.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1991_15717.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___1991_15717.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___1991_15717.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1991_15717.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1991_15717.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1991_15717.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1991_15717.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1991_15717.FStar_TypeChecker_Env.strict_args_tab)
          }  in
        let check_term lid univs1 t =
          let uu____15737 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____15737 with
          | (univs2,t1) ->
              ((let uu____15745 =
                  let uu____15747 =
                    let uu____15753 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____15753  in
                  FStar_All.pipe_left uu____15747
                    (FStar_Options.Other "Exports")
                   in
                if uu____15745
                then
                  let uu____15757 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____15759 =
                    let uu____15761 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____15761
                      (FStar_String.concat ", ")
                     in
                  let uu____15778 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____15757 uu____15759 uu____15778
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____15784 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____15784 (fun a3  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____15810 =
             let uu____15812 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____15814 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____15812 uu____15814
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____15810);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15825) ->
              let uu____15834 =
                let uu____15836 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15836  in
              if uu____15834
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____15850,uu____15851) ->
              let t =
                let uu____15863 =
                  let uu____15870 =
                    let uu____15871 =
                      let uu____15886 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____15886)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____15871  in
                  FStar_Syntax_Syntax.mk uu____15870  in
                uu____15863 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____15902,uu____15903,uu____15904) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____15914 =
                let uu____15916 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15916  in
              if uu____15914 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____15924,lbs),uu____15926) ->
              let uu____15937 =
                let uu____15939 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15939  in
              if uu____15937
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
              let uu____15962 =
                let uu____15964 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15964  in
              if uu____15962
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____15985 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____15986 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____15993 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15994 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____15995 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____15996 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____16003 -> ()  in
        let uu____16004 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____16004 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____16110) -> true
             | uu____16112 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____16142 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____16181 ->
                   let uu____16182 =
                     let uu____16189 =
                       let uu____16190 =
                         let uu____16205 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____16205)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____16190  in
                     FStar_Syntax_Syntax.mk uu____16189  in
                   uu____16182 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____16222,uu____16223) ->
            let s1 =
              let uu___2117_16233 = s  in
              let uu____16234 =
                let uu____16235 =
                  let uu____16242 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____16242)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____16235  in
              let uu____16243 =
                let uu____16246 =
                  let uu____16249 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____16249  in
                FStar_Syntax_Syntax.Assumption :: uu____16246  in
              {
                FStar_Syntax_Syntax.sigel = uu____16234;
                FStar_Syntax_Syntax.sigrng =
                  (uu___2117_16233.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____16243;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2117_16233.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___2117_16233.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____16252 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____16277 lbdef =
        match uu____16277 with
        | (uvs,t) ->
            let attrs =
              let uu____16288 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____16288
              then
                let uu____16293 =
                  let uu____16294 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____16294
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____16293 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___2130_16297 = s  in
            let uu____16298 =
              let uu____16301 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____16301  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___2130_16297.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____16298;
              FStar_Syntax_Syntax.sigmeta =
                (uu___2130_16297.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____16319 -> failwith "Impossible!"  in
        let c_opt =
          let uu____16326 = FStar_Syntax_Util.is_unit t  in
          if uu____16326
          then
            let uu____16333 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____16333
          else
            (let uu____16340 =
               let uu____16341 = FStar_Syntax_Subst.compress t  in
               uu____16341.FStar_Syntax_Syntax.n  in
             match uu____16340 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____16348,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____16372 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____16384 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____16384
            then false
            else
              (let uu____16391 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____16391
               then true
               else
                 (let uu____16398 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____16398))
         in
      let extract_sigelt s =
        (let uu____16410 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____16410
         then
           let uu____16413 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____16413
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____16420 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____16440 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____16459 ->
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
                             (lid,uu____16505,uu____16506,uu____16507,uu____16508,uu____16509)
                             ->
                             ((let uu____16519 =
                                 let uu____16522 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____16522  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____16519);
                              (let uu____16571 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____16571 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____16575,uu____16576,uu____16577,uu____16578,uu____16579)
                             ->
                             ((let uu____16587 =
                                 let uu____16590 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____16590  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____16587);
                              sigelts1)
                         | uu____16639 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____16648 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____16648
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____16658 =
                    let uu___2194_16659 = s  in
                    let uu____16660 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2194_16659.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2194_16659.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____16660;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2194_16659.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2194_16659.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____16658])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____16671 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____16671
             then []
             else
               (let uu____16678 = lbs  in
                match uu____16678 with
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
                        (fun uu____16740  ->
                           match uu____16740 with
                           | (uu____16748,t,uu____16750) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____16767  ->
                             match uu____16767 with
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
                           (fun uu____16794  ->
                              match uu____16794 with
                              | (uu____16802,t,uu____16804) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____16816,uu____16817) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____16825 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____16854 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____16854) uu____16825
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____16858 =
                    let uu___2236_16859 = s  in
                    let uu____16860 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2236_16859.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2236_16859.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____16860;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2236_16859.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2236_16859.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____16858]
                else [])
             else
               (let uu____16867 =
                  let uu___2238_16868 = s  in
                  let uu____16869 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___2238_16868.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___2238_16868.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____16869;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___2238_16868.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___2238_16868.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____16867])
         | FStar_Syntax_Syntax.Sig_new_effect uu____16872 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____16873 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____16874 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____16875 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____16888 -> [s])
         in
      let uu___2250_16889 = m  in
      let uu____16890 =
        let uu____16891 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____16891 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___2250_16889.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____16890;
        FStar_Syntax_Syntax.exports =
          (uu___2250_16889.FStar_Syntax_Syntax.exports);
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
        (fun uu____16942  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____16989  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____17004 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____17004
  
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
      (let uu____17093 = FStar_Options.debug_any ()  in
       if uu____17093
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
         let uu___2275_17109 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___2275_17109.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___2275_17109.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___2275_17109.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___2275_17109.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___2275_17109.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___2275_17109.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___2275_17109.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___2275_17109.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___2275_17109.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___2275_17109.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___2275_17109.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___2275_17109.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___2275_17109.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___2275_17109.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___2275_17109.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___2275_17109.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___2275_17109.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___2275_17109.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___2275_17109.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___2275_17109.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___2275_17109.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___2275_17109.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___2275_17109.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___2275_17109.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___2275_17109.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___2275_17109.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___2275_17109.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___2275_17109.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___2275_17109.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___2275_17109.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___2275_17109.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___2275_17109.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___2275_17109.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___2275_17109.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___2275_17109.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___2275_17109.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___2275_17109.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___2275_17109.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___2275_17109.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___2275_17109.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___2275_17109.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___2275_17109.FStar_TypeChecker_Env.strict_args_tab)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____17111 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____17111 with
       | (ses,exports,env3) ->
           ((let uu___2283_17144 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___2283_17144.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___2283_17144.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___2283_17144.FStar_Syntax_Syntax.is_interface)
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
        let uu____17173 = tc_decls env decls  in
        match uu____17173 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___2292_17204 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___2292_17204.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___2292_17204.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___2292_17204.FStar_Syntax_Syntax.is_interface)
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
        let uu____17265 = tc_partial_modul env01 m  in
        match uu____17265 with
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
                (let uu____17302 = FStar_Errors.get_err_count ()  in
                 uu____17302 = Prims.int_zero)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____17313 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____17313
                then
                  let uu____17317 =
                    let uu____17319 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____17319 then "" else " (in lax mode) "  in
                  let uu____17327 =
                    let uu____17329 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____17329
                    then
                      let uu____17333 =
                        let uu____17335 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.op_Hat uu____17335 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____17333
                    else ""  in
                  let uu____17342 =
                    let uu____17344 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____17344
                    then
                      let uu____17348 =
                        let uu____17350 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____17350 "\n"  in
                      Prims.op_Hat "\nto: " uu____17348
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____17317
                    uu____17327 uu____17342
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___2318_17364 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2318_17364.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2318_17364.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2318_17364.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2318_17364.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2318_17364.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2318_17364.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2318_17364.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2318_17364.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2318_17364.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2318_17364.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2318_17364.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2318_17364.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2318_17364.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2318_17364.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2318_17364.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2318_17364.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2318_17364.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2318_17364.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2318_17364.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2318_17364.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2318_17364.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2318_17364.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2318_17364.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2318_17364.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2318_17364.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2318_17364.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2318_17364.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2318_17364.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2318_17364.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2318_17364.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2318_17364.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___2318_17364.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2318_17364.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2318_17364.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2318_17364.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2318_17364.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2318_17364.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2318_17364.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2318_17364.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2318_17364.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2318_17364.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2318_17364.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2318_17364.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let en02 =
                    let uu___2321_17366 = en01  in
                    let uu____17367 =
                      let uu____17382 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____17382, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2321_17366.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2321_17366.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2321_17366.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2321_17366.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2321_17366.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2321_17366.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2321_17366.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2321_17366.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2321_17366.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2321_17366.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2321_17366.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2321_17366.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2321_17366.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2321_17366.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2321_17366.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2321_17366.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2321_17366.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2321_17366.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2321_17366.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2321_17366.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2321_17366.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2321_17366.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2321_17366.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2321_17366.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2321_17366.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2321_17366.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2321_17366.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2321_17366.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2321_17366.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2321_17366.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2321_17366.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____17367;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2321_17366.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2321_17366.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2321_17366.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2321_17366.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2321_17366.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2321_17366.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2321_17366.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2321_17366.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2321_17366.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___2321_17366.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2321_17366.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2321_17366.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let uu____17428 =
                    let uu____17430 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____17430  in
                  if uu____17428
                  then
                    ((let uu____17434 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____17434 (fun a4  -> ()));
                     en02)
                  else en02  in
                let uu____17438 = tc_modul en0 modul_iface true  in
                match uu____17438 with
                | (modul_iface1,env) ->
                    ((let uu___2330_17451 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___2330_17451.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___2330_17451.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___2330_17451.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___2332_17455 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___2332_17455.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___2332_17455.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___2332_17455.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____17458 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____17458 FStar_Util.smap_clear);
               (let uu____17494 =
                  ((let uu____17498 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____17498) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____17501 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____17501)
                   in
                if uu____17494 then check_exports env modul exports else ());
               (let uu____17507 =
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____17507 (fun a5  -> ()));
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
        let uu____17522 =
          let uu____17524 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____17524  in
        push_context env uu____17522  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____17545 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____17556 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____17556 with | (uu____17563,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____17588 = FStar_Options.debug_any ()  in
         if uu____17588
         then
           let uu____17591 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____17591
         else ());
        (let uu____17603 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____17603
         then
           let uu____17606 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____17606
         else ());
        (let env1 =
           let uu___2362_17612 = env  in
           let uu____17613 =
             let uu____17615 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____17615  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___2362_17612.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___2362_17612.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___2362_17612.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___2362_17612.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___2362_17612.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___2362_17612.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___2362_17612.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___2362_17612.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___2362_17612.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___2362_17612.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___2362_17612.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___2362_17612.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___2362_17612.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___2362_17612.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___2362_17612.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___2362_17612.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___2362_17612.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___2362_17612.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___2362_17612.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___2362_17612.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____17613;
             FStar_TypeChecker_Env.lax_universes =
               (uu___2362_17612.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___2362_17612.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___2362_17612.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___2362_17612.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___2362_17612.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___2362_17612.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___2362_17612.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___2362_17612.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___2362_17612.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___2362_17612.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___2362_17612.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___2362_17612.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___2362_17612.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___2362_17612.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___2362_17612.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___2362_17612.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___2362_17612.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___2362_17612.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___2362_17612.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___2362_17612.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___2362_17612.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___2362_17612.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___2362_17612.FStar_TypeChecker_Env.strict_args_tab)
           }  in
         let uu____17617 = tc_modul env1 m b  in
         match uu____17617 with
         | (m1,env2) ->
             ((let uu____17629 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____17629
               then
                 let uu____17632 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____17632
               else ());
              (let uu____17638 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____17638
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
                         let uu____17676 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____17676 with
                         | (univnames1,e) ->
                             let uu___2384_17683 = lb  in
                             let uu____17684 =
                               let uu____17687 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____17687 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2384_17683.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2384_17683.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___2384_17683.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2384_17683.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____17684;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2384_17683.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2384_17683.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___2386_17688 = se  in
                       let uu____17689 =
                         let uu____17690 =
                           let uu____17697 =
                             let uu____17698 = FStar_List.map update lbs  in
                             (b1, uu____17698)  in
                           (uu____17697, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____17690  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____17689;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___2386_17688.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___2386_17688.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___2386_17688.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___2386_17688.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____17706 -> se  in
                 let normalized_module =
                   let uu___2390_17708 = m1  in
                   let uu____17709 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___2390_17708.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____17709;
                     FStar_Syntax_Syntax.exports =
                       (uu___2390_17708.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___2390_17708.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____17710 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____17710
               else ());
              (m1, env2)))
  