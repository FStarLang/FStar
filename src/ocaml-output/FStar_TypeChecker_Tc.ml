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
  
let (tc_eff_decl :
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
                        | uu____583 ->
                            let uu____586 =
                              ((FStar_List.length ed_univs) =
                                 (FStar_List.length us))
                                &&
                                (FStar_List.forall2
                                   (fun u1  ->
                                      fun u2  ->
                                        let uu____593 =
                                          FStar_Syntax_Syntax.order_univ_name
                                            u1 u2
                                           in
                                        uu____593 = Prims.int_zero) ed_univs
                                   us)
                               in
                            if uu____586
                            then (us, bs2)
                            else
                              (let uu____604 =
                                 let uu____610 =
                                   let uu____612 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length ed_univs)
                                      in
                                   let uu____614 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length us)
                                      in
                                   FStar_Util.format3
                                     "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                     uu____612 uu____614
                                    in
                                 (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                   uu____610)
                                  in
                               let uu____618 =
                                 FStar_Ident.range_of_lid
                                   ed.FStar_Syntax_Syntax.mname
                                  in
                               FStar_Errors.raise_error uu____604 uu____618))))
          in
       match uu____463 with
       | (us,bs) ->
           let ed1 =
             let uu___101_626 = ed  in
             {
               FStar_Syntax_Syntax.cattributes =
                 (uu___101_626.FStar_Syntax_Syntax.cattributes);
               FStar_Syntax_Syntax.mname =
                 (uu___101_626.FStar_Syntax_Syntax.mname);
               FStar_Syntax_Syntax.univs = us;
               FStar_Syntax_Syntax.binders = bs;
               FStar_Syntax_Syntax.signature =
                 (uu___101_626.FStar_Syntax_Syntax.signature);
               FStar_Syntax_Syntax.ret_wp =
                 (uu___101_626.FStar_Syntax_Syntax.ret_wp);
               FStar_Syntax_Syntax.bind_wp =
                 (uu___101_626.FStar_Syntax_Syntax.bind_wp);
               FStar_Syntax_Syntax.if_then_else =
                 (uu___101_626.FStar_Syntax_Syntax.if_then_else);
               FStar_Syntax_Syntax.ite_wp =
                 (uu___101_626.FStar_Syntax_Syntax.ite_wp);
               FStar_Syntax_Syntax.stronger =
                 (uu___101_626.FStar_Syntax_Syntax.stronger);
               FStar_Syntax_Syntax.close_wp =
                 (uu___101_626.FStar_Syntax_Syntax.close_wp);
               FStar_Syntax_Syntax.trivial =
                 (uu___101_626.FStar_Syntax_Syntax.trivial);
               FStar_Syntax_Syntax.repr =
                 (uu___101_626.FStar_Syntax_Syntax.repr);
               FStar_Syntax_Syntax.return_repr =
                 (uu___101_626.FStar_Syntax_Syntax.return_repr);
               FStar_Syntax_Syntax.bind_repr =
                 (uu___101_626.FStar_Syntax_Syntax.bind_repr);
               FStar_Syntax_Syntax.actions =
                 (uu___101_626.FStar_Syntax_Syntax.actions);
               FStar_Syntax_Syntax.eff_attrs =
                 (uu___101_626.FStar_Syntax_Syntax.eff_attrs)
             }  in
           let uu____627 = FStar_Syntax_Subst.univ_var_opening us  in
           (match uu____627 with
            | (ed_univs_subst,ed_univs) ->
                let uu____646 =
                  let uu____651 =
                    FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                  FStar_Syntax_Subst.open_binders' uu____651  in
                (match uu____646 with
                 | (ed_bs,ed_bs_subst) ->
                     let ed2 =
                       let op uu____672 =
                         match uu____672 with
                         | (us1,t) ->
                             let t1 =
                               let uu____692 =
                                 FStar_Syntax_Subst.shift_subst
                                   ((FStar_List.length ed_bs) +
                                      (FStar_List.length us1)) ed_univs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____692 t  in
                             let uu____701 =
                               let uu____702 =
                                 FStar_Syntax_Subst.shift_subst
                                   (FStar_List.length us1) ed_bs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____702 t1  in
                             (us1, uu____701)
                          in
                       let uu___115_707 = ed1  in
                       let uu____708 = op ed1.FStar_Syntax_Syntax.signature
                          in
                       let uu____709 = op ed1.FStar_Syntax_Syntax.ret_wp  in
                       let uu____710 = op ed1.FStar_Syntax_Syntax.bind_wp  in
                       let uu____711 =
                         op ed1.FStar_Syntax_Syntax.if_then_else  in
                       let uu____712 = op ed1.FStar_Syntax_Syntax.ite_wp  in
                       let uu____713 = op ed1.FStar_Syntax_Syntax.stronger
                          in
                       let uu____714 = op ed1.FStar_Syntax_Syntax.close_wp
                          in
                       let uu____715 = op ed1.FStar_Syntax_Syntax.trivial  in
                       let uu____716 = op ed1.FStar_Syntax_Syntax.repr  in
                       let uu____717 = op ed1.FStar_Syntax_Syntax.return_repr
                          in
                       let uu____718 = op ed1.FStar_Syntax_Syntax.bind_repr
                          in
                       let uu____719 =
                         FStar_List.map
                           (fun a  ->
                              let uu___118_727 = a  in
                              let uu____728 =
                                let uu____729 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_defn))
                                   in
                                FStar_Pervasives_Native.snd uu____729  in
                              let uu____740 =
                                let uu____741 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_typ))
                                   in
                                FStar_Pervasives_Native.snd uu____741  in
                              {
                                FStar_Syntax_Syntax.action_name =
                                  (uu___118_727.FStar_Syntax_Syntax.action_name);
                                FStar_Syntax_Syntax.action_unqualified_name =
                                  (uu___118_727.FStar_Syntax_Syntax.action_unqualified_name);
                                FStar_Syntax_Syntax.action_univs =
                                  (uu___118_727.FStar_Syntax_Syntax.action_univs);
                                FStar_Syntax_Syntax.action_params =
                                  (uu___118_727.FStar_Syntax_Syntax.action_params);
                                FStar_Syntax_Syntax.action_defn = uu____728;
                                FStar_Syntax_Syntax.action_typ = uu____740
                              }) ed1.FStar_Syntax_Syntax.actions
                          in
                       {
                         FStar_Syntax_Syntax.cattributes =
                           (uu___115_707.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.mname =
                           (uu___115_707.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.univs =
                           (uu___115_707.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___115_707.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature = uu____708;
                         FStar_Syntax_Syntax.ret_wp = uu____709;
                         FStar_Syntax_Syntax.bind_wp = uu____710;
                         FStar_Syntax_Syntax.if_then_else = uu____711;
                         FStar_Syntax_Syntax.ite_wp = uu____712;
                         FStar_Syntax_Syntax.stronger = uu____713;
                         FStar_Syntax_Syntax.close_wp = uu____714;
                         FStar_Syntax_Syntax.trivial = uu____715;
                         FStar_Syntax_Syntax.repr = uu____716;
                         FStar_Syntax_Syntax.return_repr = uu____717;
                         FStar_Syntax_Syntax.bind_repr = uu____718;
                         FStar_Syntax_Syntax.actions = uu____719;
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___115_707.FStar_Syntax_Syntax.eff_attrs)
                       }  in
                     ((let uu____753 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env0)
                           (FStar_Options.Other "ED")
                          in
                       if uu____753
                       then
                         let uu____758 =
                           FStar_Syntax_Print.eff_decl_to_string false ed2
                            in
                         FStar_Util.print1
                           "After typechecking binders eff_decl: \n\t%s\n"
                           uu____758
                       else ());
                      (let env =
                         let uu____765 =
                           FStar_TypeChecker_Env.push_univ_vars env0 ed_univs
                            in
                         FStar_TypeChecker_Env.push_binders uu____765 ed_bs
                          in
                       let check_and_gen' comb n1 env_opt uu____800 k =
                         match uu____800 with
                         | (us1,t) ->
                             let env1 =
                               if FStar_Util.is_some env_opt
                               then
                                 FStar_All.pipe_right env_opt FStar_Util.must
                               else env  in
                             let uu____820 =
                               FStar_Syntax_Subst.open_univ_vars us1 t  in
                             (match uu____820 with
                              | (us2,t1) ->
                                  let t2 =
                                    match k with
                                    | FStar_Pervasives_Native.Some k1 ->
                                        let uu____829 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env1 us2
                                           in
                                        tc_check_trivial_guard uu____829 t1
                                          k1
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____830 =
                                          let uu____837 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            uu____837 t1
                                           in
                                        (match uu____830 with
                                         | (t2,uu____839,g) ->
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env1 g;
                                              t2))
                                     in
                                  let uu____842 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env1 t2
                                     in
                                  (match uu____842 with
                                   | (g_us,t3) ->
                                       (if (FStar_List.length g_us) <> n1
                                        then
                                          (let error =
                                             let uu____858 =
                                               FStar_Util.string_of_int n1
                                                in
                                             let uu____860 =
                                               let uu____862 =
                                                 FStar_All.pipe_right g_us
                                                   FStar_List.length
                                                  in
                                               FStar_All.pipe_right uu____862
                                                 FStar_Util.string_of_int
                                                in
                                             FStar_Util.format4
                                               "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                               (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                               comb uu____858 uu____860
                                              in
                                           FStar_Errors.raise_error
                                             (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                               error)
                                             t3.FStar_Syntax_Syntax.pos)
                                        else ();
                                        (match us2 with
                                         | [] -> (g_us, t3)
                                         | uu____877 ->
                                             let uu____878 =
                                               ((FStar_List.length us2) =
                                                  (FStar_List.length g_us))
                                                 &&
                                                 (FStar_List.forall2
                                                    (fun u1  ->
                                                       fun u2  ->
                                                         let uu____885 =
                                                           FStar_Syntax_Syntax.order_univ_name
                                                             u1 u2
                                                            in
                                                         uu____885 =
                                                           Prims.int_zero)
                                                    us2 g_us)
                                                in
                                             if uu____878
                                             then (g_us, t3)
                                             else
                                               (let uu____896 =
                                                  let uu____902 =
                                                    let uu____904 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           us2)
                                                       in
                                                    let uu____906 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           g_us)
                                                       in
                                                    FStar_Util.format4
                                                      "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                      (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      comb uu____904
                                                      uu____906
                                                     in
                                                  (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                    uu____902)
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____896
                                                  t3.FStar_Syntax_Syntax.pos)))))
                          in
                       let signature =
                         check_and_gen' "signature" Prims.int_one
                           FStar_Pervasives_Native.None
                           ed2.FStar_Syntax_Syntax.signature
                           FStar_Pervasives_Native.None
                          in
                       (let uu____914 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env0)
                            (FStar_Options.Other "ED")
                           in
                        if uu____914
                        then
                          let uu____919 =
                            FStar_Syntax_Print.tscheme_to_string signature
                             in
                          FStar_Util.print1 "Typechecked signature: %s\n"
                            uu____919
                        else ());
                       (let fresh_a_and_wp uu____935 =
                          let fail1 t =
                            let uu____948 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env ed2.FStar_Syntax_Syntax.mname t
                               in
                            FStar_Errors.raise_error uu____948
                              (FStar_Pervasives_Native.snd
                                 ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                             in
                          let uu____964 =
                            FStar_TypeChecker_Env.inst_tscheme signature  in
                          match uu____964 with
                          | (uu____975,signature1) ->
                              let uu____977 =
                                let uu____978 =
                                  FStar_Syntax_Subst.compress signature1  in
                                uu____978.FStar_Syntax_Syntax.n  in
                              (match uu____977 with
                               | FStar_Syntax_Syntax.Tm_arrow (bs1,uu____988)
                                   ->
                                   let bs2 =
                                     FStar_Syntax_Subst.open_binders bs1  in
                                   (match bs2 with
                                    | (a,uu____1017)::(wp,uu____1019)::[] ->
                                        (a, (wp.FStar_Syntax_Syntax.sort))
                                    | uu____1048 -> fail1 signature1)
                               | uu____1049 -> fail1 signature1)
                           in
                        let log_combinator s ts =
                          let uu____1063 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "ED")
                             in
                          if uu____1063
                          then
                            let uu____1068 =
                              FStar_Syntax_Print.tscheme_to_string ts  in
                            FStar_Util.print3 "Typechecked %s:%s = %s\n"
                              (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                              s uu____1068
                          else ()  in
                        let ret_wp =
                          let uu____1074 = fresh_a_and_wp ()  in
                          match uu____1074 with
                          | (a,wp_sort) ->
                              let k =
                                let uu____1090 =
                                  let uu____1099 =
                                    FStar_Syntax_Syntax.mk_binder a  in
                                  let uu____1106 =
                                    let uu____1115 =
                                      let uu____1122 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      FStar_Syntax_Syntax.null_binder
                                        uu____1122
                                       in
                                    [uu____1115]  in
                                  uu____1099 :: uu____1106  in
                                let uu____1141 =
                                  FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                FStar_Syntax_Util.arrow uu____1090 uu____1141
                                 in
                              check_and_gen' "ret_wp" Prims.int_one
                                FStar_Pervasives_Native.None
                                ed2.FStar_Syntax_Syntax.ret_wp
                                (FStar_Pervasives_Native.Some k)
                           in
                        log_combinator "ret_wp" ret_wp;
                        (let bind_wp =
                           let uu____1149 = fresh_a_and_wp ()  in
                           match uu____1149 with
                           | (a,wp_sort_a) ->
                               let uu____1162 = fresh_a_and_wp ()  in
                               (match uu____1162 with
                                | (b,wp_sort_b) ->
                                    let wp_sort_a_b =
                                      let uu____1178 =
                                        let uu____1187 =
                                          let uu____1194 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1194
                                           in
                                        [uu____1187]  in
                                      let uu____1207 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____1178
                                        uu____1207
                                       in
                                    let k =
                                      let uu____1213 =
                                        let uu____1222 =
                                          FStar_Syntax_Syntax.null_binder
                                            FStar_Syntax_Syntax.t_range
                                           in
                                        let uu____1229 =
                                          let uu____1238 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1245 =
                                            let uu____1254 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____1261 =
                                              let uu____1270 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              let uu____1277 =
                                                let uu____1286 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a_b
                                                   in
                                                [uu____1286]  in
                                              uu____1270 :: uu____1277  in
                                            uu____1254 :: uu____1261  in
                                          uu____1238 :: uu____1245  in
                                        uu____1222 :: uu____1229  in
                                      let uu____1329 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____1213
                                        uu____1329
                                       in
                                    check_and_gen' "bind_wp"
                                      (Prims.of_int (2))
                                      FStar_Pervasives_Native.None
                                      ed2.FStar_Syntax_Syntax.bind_wp
                                      (FStar_Pervasives_Native.Some k))
                            in
                         log_combinator "bind_wp" bind_wp;
                         (let if_then_else1 =
                            let uu____1337 = fresh_a_and_wp ()  in
                            match uu____1337 with
                            | (a,wp_sort_a) ->
                                let p =
                                  let uu____1351 =
                                    let uu____1354 =
                                      FStar_Ident.range_of_lid
                                        ed2.FStar_Syntax_Syntax.mname
                                       in
                                    FStar_Pervasives_Native.Some uu____1354
                                     in
                                  let uu____1355 =
                                    let uu____1356 =
                                      FStar_Syntax_Util.type_u ()  in
                                    FStar_All.pipe_right uu____1356
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_Syntax_Syntax.new_bv uu____1351
                                    uu____1355
                                   in
                                let k =
                                  let uu____1368 =
                                    let uu____1377 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____1384 =
                                      let uu____1393 =
                                        FStar_Syntax_Syntax.mk_binder p  in
                                      let uu____1400 =
                                        let uu____1409 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_sort_a
                                           in
                                        let uu____1416 =
                                          let uu____1425 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____1425]  in
                                        uu____1409 :: uu____1416  in
                                      uu____1393 :: uu____1400  in
                                    uu____1377 :: uu____1384  in
                                  let uu____1462 =
                                    FStar_Syntax_Syntax.mk_Total wp_sort_a
                                     in
                                  FStar_Syntax_Util.arrow uu____1368
                                    uu____1462
                                   in
                                check_and_gen' "if_then_else" Prims.int_one
                                  FStar_Pervasives_Native.None
                                  ed2.FStar_Syntax_Syntax.if_then_else
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "if_then_else" if_then_else1;
                          (let ite_wp =
                             let uu____1470 = fresh_a_and_wp ()  in
                             match uu____1470 with
                             | (a,wp_sort_a) ->
                                 let k =
                                   let uu____1486 =
                                     let uu____1495 =
                                       FStar_Syntax_Syntax.mk_binder a  in
                                     let uu____1502 =
                                       let uu____1511 =
                                         FStar_Syntax_Syntax.null_binder
                                           wp_sort_a
                                          in
                                       [uu____1511]  in
                                     uu____1495 :: uu____1502  in
                                   let uu____1536 =
                                     FStar_Syntax_Syntax.mk_Total wp_sort_a
                                      in
                                   FStar_Syntax_Util.arrow uu____1486
                                     uu____1536
                                    in
                                 check_and_gen' "ite_wp" Prims.int_one
                                   FStar_Pervasives_Native.None
                                   ed2.FStar_Syntax_Syntax.ite_wp
                                   (FStar_Pervasives_Native.Some k)
                              in
                           log_combinator "ite_wp" ite_wp;
                           (let stronger =
                              let uu____1544 = fresh_a_and_wp ()  in
                              match uu____1544 with
                              | (a,wp_sort_a) ->
                                  let uu____1557 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____1557 with
                                   | (t,uu____1563) ->
                                       let k =
                                         let uu____1567 =
                                           let uu____1576 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____1583 =
                                             let uu____1592 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____1599 =
                                               let uu____1608 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____1608]  in
                                             uu____1592 :: uu____1599  in
                                           uu____1576 :: uu____1583  in
                                         let uu____1639 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____1567
                                           uu____1639
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         ed2.FStar_Syntax_Syntax.stronger
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let close_wp =
                               let uu____1647 = fresh_a_and_wp ()  in
                               match uu____1647 with
                               | (a,wp_sort_a) ->
                                   let b =
                                     let uu____1661 =
                                       let uu____1664 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____1664
                                        in
                                     let uu____1665 =
                                       let uu____1666 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____1666
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____1661
                                       uu____1665
                                      in
                                   let wp_sort_b_a =
                                     let uu____1678 =
                                       let uu____1687 =
                                         let uu____1694 =
                                           FStar_Syntax_Syntax.bv_to_name b
                                            in
                                         FStar_Syntax_Syntax.null_binder
                                           uu____1694
                                          in
                                       [uu____1687]  in
                                     let uu____1707 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____1678
                                       uu____1707
                                      in
                                   let k =
                                     let uu____1713 =
                                       let uu____1722 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____1729 =
                                         let uu____1738 =
                                           FStar_Syntax_Syntax.mk_binder b
                                            in
                                         let uu____1745 =
                                           let uu____1754 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_b_a
                                              in
                                           [uu____1754]  in
                                         uu____1738 :: uu____1745  in
                                       uu____1722 :: uu____1729  in
                                     let uu____1785 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____1713
                                       uu____1785
                                      in
                                   check_and_gen' "close_wp"
                                     (Prims.of_int (2))
                                     FStar_Pervasives_Native.None
                                     ed2.FStar_Syntax_Syntax.close_wp
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "close_wp" close_wp;
                             (let trivial =
                                let uu____1793 = fresh_a_and_wp ()  in
                                match uu____1793 with
                                | (a,wp_sort_a) ->
                                    let uu____1806 =
                                      FStar_Syntax_Util.type_u ()  in
                                    (match uu____1806 with
                                     | (t,uu____1812) ->
                                         let k =
                                           let uu____1816 =
                                             let uu____1825 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____1832 =
                                               let uu____1841 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____1841]  in
                                             uu____1825 :: uu____1832  in
                                           let uu____1866 =
                                             FStar_Syntax_Syntax.mk_GTotal t
                                              in
                                           FStar_Syntax_Util.arrow uu____1816
                                             uu____1866
                                            in
                                         check_and_gen' "trivial"
                                           Prims.int_one
                                           FStar_Pervasives_Native.None
                                           ed2.FStar_Syntax_Syntax.trivial
                                           (FStar_Pervasives_Native.Some k))
                                 in
                              log_combinator "trivial" trivial;
                              (let uu____1873 =
                                 let uu____1884 =
                                   let uu____1885 =
                                     FStar_Syntax_Subst.compress
                                       (FStar_Pervasives_Native.snd
                                          ed2.FStar_Syntax_Syntax.repr)
                                      in
                                   uu____1885.FStar_Syntax_Syntax.n  in
                                 match uu____1884 with
                                 | FStar_Syntax_Syntax.Tm_unknown  ->
                                     ((ed2.FStar_Syntax_Syntax.repr),
                                       (ed2.FStar_Syntax_Syntax.return_repr),
                                       (ed2.FStar_Syntax_Syntax.bind_repr),
                                       (ed2.FStar_Syntax_Syntax.actions))
                                 | uu____1904 ->
                                     let repr =
                                       let uu____1906 = fresh_a_and_wp ()  in
                                       match uu____1906 with
                                       | (a,wp_sort_a) ->
                                           let uu____1919 =
                                             FStar_Syntax_Util.type_u ()  in
                                           (match uu____1919 with
                                            | (t,uu____1925) ->
                                                let k =
                                                  let uu____1929 =
                                                    let uu____1938 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        a
                                                       in
                                                    let uu____1945 =
                                                      let uu____1954 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          wp_sort_a
                                                         in
                                                      [uu____1954]  in
                                                    uu____1938 :: uu____1945
                                                     in
                                                  let uu____1979 =
                                                    FStar_Syntax_Syntax.mk_GTotal
                                                      t
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____1929 uu____1979
                                                   in
                                                check_and_gen' "repr"
                                                  Prims.int_one
                                                  FStar_Pervasives_Native.None
                                                  ed2.FStar_Syntax_Syntax.repr
                                                  (FStar_Pervasives_Native.Some
                                                     k))
                                        in
                                     (log_combinator "repr" repr;
                                      (let mk_repr' t wp =
                                         let uu____1999 =
                                           FStar_TypeChecker_Env.inst_tscheme
                                             repr
                                            in
                                         match uu____1999 with
                                         | (uu____2006,repr1) ->
                                             let repr2 =
                                               FStar_TypeChecker_Normalize.normalize
                                                 [FStar_TypeChecker_Env.EraseUniverses;
                                                 FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                 env repr1
                                                in
                                             let uu____2009 =
                                               let uu____2016 =
                                                 let uu____2017 =
                                                   let uu____2034 =
                                                     let uu____2045 =
                                                       FStar_All.pipe_right t
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     let uu____2062 =
                                                       let uu____2073 =
                                                         FStar_All.pipe_right
                                                           wp
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____2073]  in
                                                     uu____2045 :: uu____2062
                                                      in
                                                   (repr2, uu____2034)  in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____2017
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____2016
                                                in
                                             uu____2009
                                               FStar_Pervasives_Native.None
                                               FStar_Range.dummyRange
                                          in
                                       let mk_repr a wp =
                                         let uu____2139 =
                                           FStar_Syntax_Syntax.bv_to_name a
                                            in
                                         mk_repr' uu____2139 wp  in
                                       let destruct_repr t =
                                         let uu____2154 =
                                           let uu____2155 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____2155.FStar_Syntax_Syntax.n
                                            in
                                         match uu____2154 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____2166,(t1,uu____2168)::
                                              (wp,uu____2170)::[])
                                             -> (t1, wp)
                                         | uu____2229 ->
                                             failwith "Unexpected repr type"
                                          in
                                       let return_repr =
                                         let uu____2240 = fresh_a_and_wp ()
                                            in
                                         match uu____2240 with
                                         | (a,uu____2248) ->
                                             let x_a =
                                               let uu____2254 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   a
                                                  in
                                               FStar_Syntax_Syntax.gen_bv
                                                 "x_a"
                                                 FStar_Pervasives_Native.None
                                                 uu____2254
                                                in
                                             let res =
                                               let wp =
                                                 let uu____2262 =
                                                   let uu____2267 =
                                                     let uu____2268 =
                                                       FStar_TypeChecker_Env.inst_tscheme
                                                         ret_wp
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____2268
                                                       FStar_Pervasives_Native.snd
                                                      in
                                                   let uu____2277 =
                                                     let uu____2278 =
                                                       let uu____2287 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____2287
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     let uu____2296 =
                                                       let uu____2307 =
                                                         let uu____2316 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x_a
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____2316
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____2307]  in
                                                     uu____2278 :: uu____2296
                                                      in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     uu____2267 uu____2277
                                                    in
                                                 uu____2262
                                                   FStar_Pervasives_Native.None
                                                   FStar_Range.dummyRange
                                                  in
                                               mk_repr a wp  in
                                             let k =
                                               let uu____2352 =
                                                 let uu____2361 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     a
                                                    in
                                                 let uu____2368 =
                                                   let uu____2377 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       x_a
                                                      in
                                                   [uu____2377]  in
                                                 uu____2361 :: uu____2368  in
                                               let uu____2402 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   res
                                                  in
                                               FStar_Syntax_Util.arrow
                                                 uu____2352 uu____2402
                                                in
                                             let uu____2405 =
                                               FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                 env k
                                                in
                                             (match uu____2405 with
                                              | (k1,uu____2413,uu____2414) ->
                                                  let env1 =
                                                    let uu____2418 =
                                                      FStar_TypeChecker_Env.set_range
                                                        env
                                                        (FStar_Pervasives_Native.snd
                                                           ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Pervasives_Native.Some
                                                      uu____2418
                                                     in
                                                  check_and_gen'
                                                    "return_repr"
                                                    Prims.int_one env1
                                                    ed2.FStar_Syntax_Syntax.return_repr
                                                    (FStar_Pervasives_Native.Some
                                                       k1))
                                          in
                                       log_combinator "return_repr"
                                         return_repr;
                                       (let bind_repr =
                                          let r =
                                            let uu____2429 =
                                              FStar_Syntax_Syntax.lid_as_fv
                                                FStar_Parser_Const.range_0
                                                FStar_Syntax_Syntax.delta_constant
                                                FStar_Pervasives_Native.None
                                               in
                                            FStar_All.pipe_right uu____2429
                                              FStar_Syntax_Syntax.fv_to_tm
                                             in
                                          let uu____2430 = fresh_a_and_wp ()
                                             in
                                          match uu____2430 with
                                          | (a,wp_sort_a) ->
                                              let uu____2443 =
                                                fresh_a_and_wp ()  in
                                              (match uu____2443 with
                                               | (b,wp_sort_b) ->
                                                   let wp_sort_a_b =
                                                     let uu____2459 =
                                                       let uu____2468 =
                                                         let uu____2475 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             a
                                                            in
                                                         FStar_Syntax_Syntax.null_binder
                                                           uu____2475
                                                          in
                                                       [uu____2468]  in
                                                     let uu____2488 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         wp_sort_b
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____2459 uu____2488
                                                      in
                                                   let wp_f =
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "wp_f"
                                                       FStar_Pervasives_Native.None
                                                       wp_sort_a
                                                      in
                                                   let wp_g =
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "wp_g"
                                                       FStar_Pervasives_Native.None
                                                       wp_sort_a_b
                                                      in
                                                   let x_a =
                                                     let uu____2496 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "x_a"
                                                       FStar_Pervasives_Native.None
                                                       uu____2496
                                                      in
                                                   let wp_g_x =
                                                     let uu____2501 =
                                                       let uu____2506 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_g
                                                          in
                                                       let uu____2507 =
                                                         let uu____2508 =
                                                           let uu____2517 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x_a
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____2517
                                                             FStar_Syntax_Syntax.as_arg
                                                            in
                                                         [uu____2508]  in
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         uu____2506
                                                         uu____2507
                                                        in
                                                     uu____2501
                                                       FStar_Pervasives_Native.None
                                                       FStar_Range.dummyRange
                                                      in
                                                   let res =
                                                     let wp =
                                                       let uu____2548 =
                                                         let uu____2553 =
                                                           let uu____2554 =
                                                             FStar_TypeChecker_Env.inst_tscheme
                                                               bind_wp
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____2554
                                                             FStar_Pervasives_Native.snd
                                                            in
                                                         let uu____2563 =
                                                           let uu____2564 =
                                                             let uu____2567 =
                                                               let uu____2570
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   a
                                                                  in
                                                               let uu____2571
                                                                 =
                                                                 let uu____2574
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    b
                                                                    in
                                                                 let uu____2575
                                                                   =
                                                                   let uu____2578
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                   let uu____2579
                                                                    =
                                                                    let uu____2582
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                    [uu____2582]
                                                                     in
                                                                   uu____2578
                                                                    ::
                                                                    uu____2579
                                                                    in
                                                                 uu____2574
                                                                   ::
                                                                   uu____2575
                                                                  in
                                                               uu____2570 ::
                                                                 uu____2571
                                                                in
                                                             r :: uu____2567
                                                              in
                                                           FStar_List.map
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____2564
                                                            in
                                                         FStar_Syntax_Syntax.mk_Tm_app
                                                           uu____2553
                                                           uu____2563
                                                          in
                                                       uu____2548
                                                         FStar_Pervasives_Native.None
                                                         FStar_Range.dummyRange
                                                        in
                                                     mk_repr b wp  in
                                                   let maybe_range_arg =
                                                     let uu____2600 =
                                                       FStar_Util.for_some
                                                         (FStar_Syntax_Util.attr_eq
                                                            FStar_Syntax_Util.dm4f_bind_range_attr)
                                                         ed2.FStar_Syntax_Syntax.eff_attrs
                                                        in
                                                     if uu____2600
                                                     then
                                                       let uu____2611 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           FStar_Syntax_Syntax.t_range
                                                          in
                                                       let uu____2618 =
                                                         let uu____2627 =
                                                           FStar_Syntax_Syntax.null_binder
                                                             FStar_Syntax_Syntax.t_range
                                                            in
                                                         [uu____2627]  in
                                                       uu____2611 ::
                                                         uu____2618
                                                     else []  in
                                                   let k =
                                                     let uu____2663 =
                                                       let uu____2672 =
                                                         let uu____2681 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             a
                                                            in
                                                         let uu____2688 =
                                                           let uu____2697 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               b
                                                              in
                                                           [uu____2697]  in
                                                         uu____2681 ::
                                                           uu____2688
                                                          in
                                                       let uu____2722 =
                                                         let uu____2731 =
                                                           let uu____2740 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               wp_f
                                                              in
                                                           let uu____2747 =
                                                             let uu____2756 =
                                                               let uu____2763
                                                                 =
                                                                 let uu____2764
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f
                                                                    in
                                                                 mk_repr a
                                                                   uu____2764
                                                                  in
                                                               FStar_Syntax_Syntax.null_binder
                                                                 uu____2763
                                                                in
                                                             let uu____2765 =
                                                               let uu____2774
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp_g
                                                                  in
                                                               let uu____2781
                                                                 =
                                                                 let uu____2790
                                                                   =
                                                                   let uu____2797
                                                                    =
                                                                    let uu____2798
                                                                    =
                                                                    let uu____2807
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____2807]
                                                                     in
                                                                    let uu____2826
                                                                    =
                                                                    let uu____2829
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____2829
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____2798
                                                                    uu____2826
                                                                     in
                                                                   FStar_Syntax_Syntax.null_binder
                                                                    uu____2797
                                                                    in
                                                                 [uu____2790]
                                                                  in
                                                               uu____2774 ::
                                                                 uu____2781
                                                                in
                                                             uu____2756 ::
                                                               uu____2765
                                                              in
                                                           uu____2740 ::
                                                             uu____2747
                                                            in
                                                         FStar_List.append
                                                           maybe_range_arg
                                                           uu____2731
                                                          in
                                                       FStar_List.append
                                                         uu____2672
                                                         uu____2722
                                                        in
                                                     let uu____2874 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         res
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____2663 uu____2874
                                                      in
                                                   let uu____2877 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env k
                                                      in
                                                   (match uu____2877 with
                                                    | (k1,uu____2885,uu____2886)
                                                        ->
                                                        let env1 =
                                                          FStar_TypeChecker_Env.set_range
                                                            env
                                                            (FStar_Pervasives_Native.snd
                                                               ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                           in
                                                        let env2 =
                                                          FStar_All.pipe_right
                                                            (let uu___310_2898
                                                               = env1  in
                                                             {
                                                               FStar_TypeChecker_Env.solver
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.solver);
                                                               FStar_TypeChecker_Env.range
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.range);
                                                               FStar_TypeChecker_Env.curmodule
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.curmodule);
                                                               FStar_TypeChecker_Env.gamma
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.gamma);
                                                               FStar_TypeChecker_Env.gamma_sig
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.gamma_sig);
                                                               FStar_TypeChecker_Env.gamma_cache
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.gamma_cache);
                                                               FStar_TypeChecker_Env.modules
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.modules);
                                                               FStar_TypeChecker_Env.expected_typ
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.expected_typ);
                                                               FStar_TypeChecker_Env.sigtab
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.sigtab);
                                                               FStar_TypeChecker_Env.attrtab
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.attrtab);
                                                               FStar_TypeChecker_Env.is_pattern
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.is_pattern);
                                                               FStar_TypeChecker_Env.instantiate_imp
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.instantiate_imp);
                                                               FStar_TypeChecker_Env.effects
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.effects);
                                                               FStar_TypeChecker_Env.generalize
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.generalize);
                                                               FStar_TypeChecker_Env.letrecs
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.letrecs);
                                                               FStar_TypeChecker_Env.top_level
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.top_level);
                                                               FStar_TypeChecker_Env.check_uvars
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.check_uvars);
                                                               FStar_TypeChecker_Env.use_eq
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.use_eq);
                                                               FStar_TypeChecker_Env.is_iface
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.is_iface);
                                                               FStar_TypeChecker_Env.admit
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.admit);
                                                               FStar_TypeChecker_Env.lax
                                                                 = true;
                                                               FStar_TypeChecker_Env.lax_universes
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.lax_universes);
                                                               FStar_TypeChecker_Env.phase1
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.phase1);
                                                               FStar_TypeChecker_Env.failhard
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.failhard);
                                                               FStar_TypeChecker_Env.nosynth
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.nosynth);
                                                               FStar_TypeChecker_Env.uvar_subtyping
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.uvar_subtyping);
                                                               FStar_TypeChecker_Env.tc_term
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.tc_term);
                                                               FStar_TypeChecker_Env.type_of
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.type_of);
                                                               FStar_TypeChecker_Env.universe_of
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.universe_of);
                                                               FStar_TypeChecker_Env.check_type_of
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.check_type_of);
                                                               FStar_TypeChecker_Env.use_bv_sorts
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.use_bv_sorts);
                                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                               FStar_TypeChecker_Env.normalized_eff_names
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.normalized_eff_names);
                                                               FStar_TypeChecker_Env.fv_delta_depths
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.fv_delta_depths);
                                                               FStar_TypeChecker_Env.proof_ns
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.proof_ns);
                                                               FStar_TypeChecker_Env.synth_hook
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.synth_hook);
                                                               FStar_TypeChecker_Env.splice
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.splice);
                                                               FStar_TypeChecker_Env.postprocess
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.postprocess);
                                                               FStar_TypeChecker_Env.is_native_tactic
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.is_native_tactic);
                                                               FStar_TypeChecker_Env.identifier_info
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.identifier_info);
                                                               FStar_TypeChecker_Env.tc_hooks
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.tc_hooks);
                                                               FStar_TypeChecker_Env.dsenv
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.dsenv);
                                                               FStar_TypeChecker_Env.nbe
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.nbe);
                                                               FStar_TypeChecker_Env.strict_args_tab
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.strict_args_tab);
                                                               FStar_TypeChecker_Env.erasable_types_tab
                                                                 =
                                                                 (uu___310_2898.FStar_TypeChecker_Env.erasable_types_tab)
                                                             })
                                                            (fun _2900  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _2900)
                                                           in
                                                        check_and_gen'
                                                          "bind_repr"
                                                          (Prims.of_int (2))
                                                          env2
                                                          ed2.FStar_Syntax_Syntax.bind_repr
                                                          (FStar_Pervasives_Native.Some
                                                             k1)))
                                           in
                                        log_combinator "bind_repr" bind_repr;
                                        (let actions =
                                           let check_action act =
                                             if
                                               (FStar_List.length
                                                  act.FStar_Syntax_Syntax.action_params)
                                                 <> Prims.int_zero
                                             then
                                               failwith
                                                 "tc_eff_decl: expected action_params to be empty"
                                             else ();
                                             (let uu____2927 =
                                                if
                                                  act.FStar_Syntax_Syntax.action_univs
                                                    = []
                                                then (env, act)
                                                else
                                                  (let uu____2941 =
                                                     FStar_Syntax_Subst.univ_var_opening
                                                       act.FStar_Syntax_Syntax.action_univs
                                                      in
                                                   match uu____2941 with
                                                   | (usubst,uvs) ->
                                                       let uu____2964 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env uvs
                                                          in
                                                       let uu____2965 =
                                                         let uu___323_2966 =
                                                           act  in
                                                         let uu____2967 =
                                                           FStar_Syntax_Subst.subst
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____2968 =
                                                           FStar_Syntax_Subst.subst
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_typ
                                                            in
                                                         {
                                                           FStar_Syntax_Syntax.action_name
                                                             =
                                                             (uu___323_2966.FStar_Syntax_Syntax.action_name);
                                                           FStar_Syntax_Syntax.action_unqualified_name
                                                             =
                                                             (uu___323_2966.FStar_Syntax_Syntax.action_unqualified_name);
                                                           FStar_Syntax_Syntax.action_univs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.action_params
                                                             =
                                                             (uu___323_2966.FStar_Syntax_Syntax.action_params);
                                                           FStar_Syntax_Syntax.action_defn
                                                             = uu____2967;
                                                           FStar_Syntax_Syntax.action_typ
                                                             = uu____2968
                                                         }  in
                                                       (uu____2964,
                                                         uu____2965))
                                                 in
                                              match uu____2927 with
                                              | (env1,act1) ->
                                                  let act_typ =
                                                    let uu____2972 =
                                                      let uu____2973 =
                                                        FStar_Syntax_Subst.compress
                                                          act1.FStar_Syntax_Syntax.action_typ
                                                         in
                                                      uu____2973.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____2972 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs1,c) ->
                                                        let c1 =
                                                          FStar_Syntax_Util.comp_to_comp_typ
                                                            c
                                                           in
                                                        let uu____2999 =
                                                          FStar_Ident.lid_equals
                                                            c1.FStar_Syntax_Syntax.effect_name
                                                            ed2.FStar_Syntax_Syntax.mname
                                                           in
                                                        if uu____2999
                                                        then
                                                          let uu____3002 =
                                                            let uu____3005 =
                                                              let uu____3006
                                                                =
                                                                let uu____3007
                                                                  =
                                                                  FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____3007
                                                                 in
                                                              mk_repr'
                                                                c1.FStar_Syntax_Syntax.result_typ
                                                                uu____3006
                                                               in
                                                            FStar_Syntax_Syntax.mk_Total
                                                              uu____3005
                                                             in
                                                          FStar_Syntax_Util.arrow
                                                            bs1 uu____3002
                                                        else
                                                          act1.FStar_Syntax_Syntax.action_typ
                                                    | uu____3030 ->
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  let uu____3031 =
                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                      env1 act_typ
                                                     in
                                                  (match uu____3031 with
                                                   | (act_typ1,uu____3039,g_t)
                                                       ->
                                                       let env' =
                                                         let uu___340_3042 =
                                                           FStar_TypeChecker_Env.set_expected_typ
                                                             env1 act_typ1
                                                            in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             = false;
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.lax);
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.nbe);
                                                           FStar_TypeChecker_Env.strict_args_tab
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.strict_args_tab);
                                                           FStar_TypeChecker_Env.erasable_types_tab
                                                             =
                                                             (uu___340_3042.FStar_TypeChecker_Env.erasable_types_tab)
                                                         }  in
                                                       ((let uu____3045 =
                                                           FStar_TypeChecker_Env.debug
                                                             env1
                                                             (FStar_Options.Other
                                                                "ED")
                                                            in
                                                         if uu____3045
                                                         then
                                                           let uu____3049 =
                                                             FStar_Ident.text_of_lid
                                                               act1.FStar_Syntax_Syntax.action_name
                                                              in
                                                           let uu____3051 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act1.FStar_Syntax_Syntax.action_defn
                                                              in
                                                           let uu____3053 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ1
                                                              in
                                                           FStar_Util.print3
                                                             "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                             uu____3049
                                                             uu____3051
                                                             uu____3053
                                                         else ());
                                                        (let uu____3058 =
                                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                             env'
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         match uu____3058
                                                         with
                                                         | (act_defn,uu____3066,g_a)
                                                             ->
                                                             let act_defn1 =
                                                               FStar_TypeChecker_Normalize.normalize
                                                                 [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant]
                                                                 env1
                                                                 act_defn
                                                                in
                                                             let act_typ2 =
                                                               FStar_TypeChecker_Normalize.normalize
                                                                 [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant;
                                                                 FStar_TypeChecker_Env.Eager_unfolding;
                                                                 FStar_TypeChecker_Env.Beta]
                                                                 env1
                                                                 act_typ1
                                                                in
                                                             let uu____3070 =
                                                               let act_typ3 =
                                                                 FStar_Syntax_Subst.compress
                                                                   act_typ2
                                                                  in
                                                               match 
                                                                 act_typ3.FStar_Syntax_Syntax.n
                                                               with
                                                               | FStar_Syntax_Syntax.Tm_arrow
                                                                   (bs1,c) ->
                                                                   let uu____3106
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                   (match uu____3106
                                                                    with
                                                                    | 
                                                                    (bs2,uu____3118)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____3125
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____3125
                                                                     in
                                                                    let uu____3128
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____3128
                                                                    with
                                                                    | 
                                                                    (k1,uu____3142,g)
                                                                    ->
                                                                    (k1, g)))
                                                               | uu____3146
                                                                   ->
                                                                   let uu____3147
                                                                    =
                                                                    let uu____3153
                                                                    =
                                                                    let uu____3155
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____3157
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____3155
                                                                    uu____3157
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____3153)
                                                                     in
                                                                   FStar_Errors.raise_error
                                                                    uu____3147
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                in
                                                             (match uu____3070
                                                              with
                                                              | (expected_k,g_k)
                                                                  ->
                                                                  let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k
                                                                     in
                                                                  ((let uu____3175
                                                                    =
                                                                    let uu____3176
                                                                    =
                                                                    let uu____3177
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____3177
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____3176
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____3175);
                                                                   (let act_typ3
                                                                    =
                                                                    let uu____3179
                                                                    =
                                                                    let uu____3180
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____3180.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____3179
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____3205
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____3205
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____3212
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____3212
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____3232
                                                                    =
                                                                    let uu____3233
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____3233]
                                                                     in
                                                                    let uu____3234
                                                                    =
                                                                    let uu____3245
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____3245]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____3232;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____3234;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____3270
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____3270))
                                                                    | 
                                                                    uu____3273
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____3275
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____3297
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____3297))
                                                                     in
                                                                    match uu____3275
                                                                    with
                                                                    | 
                                                                    (univs1,act_defn2)
                                                                    ->
                                                                    let act_typ4
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.Beta]
                                                                    env1
                                                                    act_typ3
                                                                     in
                                                                    let act_typ5
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    univs1
                                                                    act_typ4
                                                                     in
                                                                    let uu___390_3316
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___390_3316.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___390_3316.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___390_3316.FStar_Syntax_Syntax.action_params);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn2;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    act_typ5
                                                                    })))))))
                                              in
                                           FStar_All.pipe_right
                                             ed2.FStar_Syntax_Syntax.actions
                                             (FStar_List.map check_action)
                                            in
                                         (repr, return_repr, bind_repr,
                                           actions)))))
                                  in
                               match uu____1873 with
                               | (repr,return_repr,bind_repr,actions) ->
                                   let cl ts =
                                     let ts1 =
                                       FStar_Syntax_Subst.close_tscheme ed_bs
                                         ts
                                        in
                                     let ed_univs_closing =
                                       FStar_Syntax_Subst.univ_var_closing
                                         ed_univs
                                        in
                                     let uu____3341 =
                                       FStar_Syntax_Subst.shift_subst
                                         (FStar_List.length ed_bs)
                                         ed_univs_closing
                                        in
                                     FStar_Syntax_Subst.subst_tscheme
                                       uu____3341 ts1
                                      in
                                   let ed3 =
                                     let uu___402_3351 = ed2  in
                                     let uu____3352 = cl signature  in
                                     let uu____3353 = cl ret_wp  in
                                     let uu____3354 = cl bind_wp  in
                                     let uu____3355 = cl if_then_else1  in
                                     let uu____3356 = cl ite_wp  in
                                     let uu____3357 = cl stronger  in
                                     let uu____3358 = cl close_wp  in
                                     let uu____3359 = cl trivial  in
                                     let uu____3360 = cl repr  in
                                     let uu____3361 = cl return_repr  in
                                     let uu____3362 = cl bind_repr  in
                                     let uu____3363 =
                                       FStar_List.map
                                         (fun a  ->
                                            let uu___405_3371 = a  in
                                            let uu____3372 =
                                              let uu____3373 =
                                                cl
                                                  ((a.FStar_Syntax_Syntax.action_univs),
                                                    (a.FStar_Syntax_Syntax.action_defn))
                                                 in
                                              FStar_All.pipe_right uu____3373
                                                FStar_Pervasives_Native.snd
                                               in
                                            let uu____3398 =
                                              let uu____3399 =
                                                cl
                                                  ((a.FStar_Syntax_Syntax.action_univs),
                                                    (a.FStar_Syntax_Syntax.action_typ))
                                                 in
                                              FStar_All.pipe_right uu____3399
                                                FStar_Pervasives_Native.snd
                                               in
                                            {
                                              FStar_Syntax_Syntax.action_name
                                                =
                                                (uu___405_3371.FStar_Syntax_Syntax.action_name);
                                              FStar_Syntax_Syntax.action_unqualified_name
                                                =
                                                (uu___405_3371.FStar_Syntax_Syntax.action_unqualified_name);
                                              FStar_Syntax_Syntax.action_univs
                                                =
                                                (uu___405_3371.FStar_Syntax_Syntax.action_univs);
                                              FStar_Syntax_Syntax.action_params
                                                =
                                                (uu___405_3371.FStar_Syntax_Syntax.action_params);
                                              FStar_Syntax_Syntax.action_defn
                                                = uu____3372;
                                              FStar_Syntax_Syntax.action_typ
                                                = uu____3398
                                            }) actions
                                        in
                                     {
                                       FStar_Syntax_Syntax.cattributes =
                                         (uu___402_3351.FStar_Syntax_Syntax.cattributes);
                                       FStar_Syntax_Syntax.mname =
                                         (uu___402_3351.FStar_Syntax_Syntax.mname);
                                       FStar_Syntax_Syntax.univs =
                                         (uu___402_3351.FStar_Syntax_Syntax.univs);
                                       FStar_Syntax_Syntax.binders =
                                         (uu___402_3351.FStar_Syntax_Syntax.binders);
                                       FStar_Syntax_Syntax.signature =
                                         uu____3352;
                                       FStar_Syntax_Syntax.ret_wp =
                                         uu____3353;
                                       FStar_Syntax_Syntax.bind_wp =
                                         uu____3354;
                                       FStar_Syntax_Syntax.if_then_else =
                                         uu____3355;
                                       FStar_Syntax_Syntax.ite_wp =
                                         uu____3356;
                                       FStar_Syntax_Syntax.stronger =
                                         uu____3357;
                                       FStar_Syntax_Syntax.close_wp =
                                         uu____3358;
                                       FStar_Syntax_Syntax.trivial =
                                         uu____3359;
                                       FStar_Syntax_Syntax.repr = uu____3360;
                                       FStar_Syntax_Syntax.return_repr =
                                         uu____3361;
                                       FStar_Syntax_Syntax.bind_repr =
                                         uu____3362;
                                       FStar_Syntax_Syntax.actions =
                                         uu____3363;
                                       FStar_Syntax_Syntax.eff_attrs =
                                         (uu___402_3351.FStar_Syntax_Syntax.eff_attrs)
                                     }  in
                                   ((let uu____3425 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "ED")
                                        in
                                     if uu____3425
                                     then
                                       let uu____3430 =
                                         FStar_Syntax_Print.eff_decl_to_string
                                           false ed3
                                          in
                                       FStar_Util.print1
                                         "Typechecked effect declaration:\n\t%s\n"
                                         uu____3430
                                     else ());
                                    ed3))))))))))))))
  
let (cps_and_elaborate :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun ed  ->
      let uu____3457 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature)
         in
      match uu____3457 with
      | (effect_binders_un,signature_un) ->
          let uu____3478 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____3478 with
           | (effect_binders,env1,uu____3497) ->
               let uu____3498 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____3498 with
                | (signature,uu____3514) ->
                    let raise_error1 uu____3530 =
                      match uu____3530 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____3566  ->
                           match uu____3566 with
                           | (bv,qual) ->
                               let uu____3585 =
                                 let uu___430_3586 = bv  in
                                 let uu____3587 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___430_3586.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___430_3586.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____3587
                                 }  in
                               (uu____3585, qual)) effect_binders
                       in
                    let uu____3592 =
                      let uu____3599 =
                        let uu____3600 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____3600.FStar_Syntax_Syntax.n  in
                      match uu____3599 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____3610)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____3642 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____3592 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____3668 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____3668
                           then
                             let uu____3671 =
                               let uu____3674 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____3674  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____3671
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____3722 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____3722 with
                           | (t2,comp,uu____3735) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____3744 =
                           open_and_check env1 []
                             (FStar_Pervasives_Native.snd
                                ed.FStar_Syntax_Syntax.repr)
                            in
                         (match uu____3744 with
                          | (repr,_comp) ->
                              ((let uu____3772 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____3772
                                then
                                  let uu____3776 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____3776
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
                                let uu____3783 =
                                  recheck_debug "*" env1 wp_type  in
                                let wp_a =
                                  let uu____3786 =
                                    let uu____3787 =
                                      let uu____3788 =
                                        let uu____3805 =
                                          let uu____3816 =
                                            let uu____3825 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____3828 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____3825, uu____3828)  in
                                          [uu____3816]  in
                                        (wp_type, uu____3805)  in
                                      FStar_Syntax_Syntax.Tm_app uu____3788
                                       in
                                    mk1 uu____3787  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta] env1
                                    uu____3786
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____3876 =
                                      let uu____3883 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____3883)  in
                                    let uu____3889 =
                                      let uu____3898 =
                                        let uu____3905 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____3905
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____3898]  in
                                    uu____3876 :: uu____3889  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let uu____3942 =
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
                                  let uu____4008 = item  in
                                  match uu____4008 with
                                  | (u_item,item1) ->
                                      let uu____4023 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____4023 with
                                       | (item2,item_comp) ->
                                           ((let uu____4039 =
                                               let uu____4041 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____4041
                                                in
                                             if uu____4039
                                             then
                                               let uu____4044 =
                                                 let uu____4050 =
                                                   let uu____4052 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____4054 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____4052 uu____4054
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____4050)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____4044
                                             else ());
                                            (let uu____4060 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____4060 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let uu____4078 =
                                                   recheck_debug "*" env2
                                                     item_wp
                                                    in
                                                 let uu____4080 =
                                                   recheck_debug "_" env2
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab))))
                                   in
                                let uu____4082 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____4082 with
                                | (dmff_env1,uu____4108,bind_wp,bind_elab) ->
                                    let uu____4111 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____4111 with
                                     | (dmff_env2,uu____4137,return_wp,return_elab)
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
                                           let uu____4146 =
                                             let uu____4147 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____4147.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4146 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____4205 =
                                                 let uu____4224 =
                                                   let uu____4229 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____4229
                                                    in
                                                 match uu____4224 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____4311 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____4205 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____4365 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____4365 [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____4388 =
                                                          let uu____4389 =
                                                            let uu____4406 =
                                                              let uu____4417
                                                                =
                                                                let uu____4426
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11)
                                                                   in
                                                                let uu____4431
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____4426,
                                                                  uu____4431)
                                                                 in
                                                              [uu____4417]
                                                               in
                                                            (wp_type,
                                                              uu____4406)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____4389
                                                           in
                                                        mk1 uu____4388  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Env.Beta]
                                                        env0 raw_wp_b1
                                                       in
                                                    let uu____4467 =
                                                      let uu____4476 =
                                                        let uu____4477 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____4477
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____4476
                                                       in
                                                    (match uu____4467 with
                                                     | (bs1,body2,what') ->
                                                         let fail1 uu____4500
                                                           =
                                                           let error_msg =
                                                             let uu____4503 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2
                                                                in
                                                             let uu____4505 =
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
                                                               uu____4503
                                                               uu____4505
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
                                                               ((let uu____4515
                                                                   =
                                                                   let uu____4517
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                   Prims.op_Negation
                                                                    uu____4517
                                                                    in
                                                                 if
                                                                   uu____4515
                                                                 then
                                                                   fail1 ()
                                                                 else ());
                                                                (let uu____4522
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
                                                                   uu____4522
                                                                   (fun a1 
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
                                                             let uu____4551 =
                                                               let uu____4556
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp
                                                                  in
                                                               let uu____4557
                                                                 =
                                                                 let uu____4558
                                                                   =
                                                                   let uu____4567
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                   (uu____4567,
                                                                    FStar_Pervasives_Native.None)
                                                                    in
                                                                 [uu____4558]
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____4556
                                                                 uu____4557
                                                                in
                                                             uu____4551
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange
                                                              in
                                                           let uu____4602 =
                                                             let uu____4603 =
                                                               let uu____4612
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp
                                                                  in
                                                               [uu____4612]
                                                                in
                                                             b11 ::
                                                               uu____4603
                                                              in
                                                           let uu____4637 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what
                                                              in
                                                           FStar_Syntax_Util.abs
                                                             uu____4602
                                                             uu____4637
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____4640 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let return_wp1 =
                                           let uu____4648 =
                                             let uu____4649 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____4649.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4648 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____4707 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____4707
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____4728 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let bind_wp1 =
                                           let uu____4736 =
                                             let uu____4737 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____4737.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4736 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_constant_at_level
                                                      Prims.int_one)
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let uu____4771 =
                                                 let uu____4772 =
                                                   let uu____4781 =
                                                     let uu____4788 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____4788
                                                      in
                                                   [uu____4781]  in
                                                 FStar_List.append uu____4772
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____4771 body what
                                           | uu____4807 ->
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
                                             (let uu____4837 =
                                                let uu____4838 =
                                                  let uu____4839 =
                                                    let uu____4856 =
                                                      let uu____4867 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____4867
                                                       in
                                                    (t, uu____4856)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____4839
                                                   in
                                                mk1 uu____4838  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____4837)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____4925 = f a2  in
                                               [uu____4925]
                                           | x::xs ->
                                               let uu____4936 =
                                                 apply_last1 f xs  in
                                               x :: uu____4936
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
                                           let uu____4970 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____4970 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____5000 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____5000
                                                 then
                                                   let uu____5003 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____5003
                                                 else ());
                                                (let uu____5008 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____5008))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____5017 =
                                                 let uu____5022 = mk_lid name
                                                    in
                                                 let uu____5023 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____5022 uu____5023
                                                  in
                                               (match uu____5017 with
                                                | (sigelt,fv) ->
                                                    ((let uu____5027 =
                                                        let uu____5030 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____5030
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____5027);
                                                     fv))
                                            in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp2 =
                                           register "return_wp" return_wp1
                                            in
                                         ((let uu____5084 =
                                             let uu____5087 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.PushOptions
                                                       (FStar_Pervasives_Native.Some
                                                          "--admit_smt_queries true")))
                                                in
                                             let uu____5090 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____5087 :: uu____5090  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____5084);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           (let uu____5142 =
                                              let uu____5145 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     FStar_Syntax_Syntax.PopOptions)
                                                 in
                                              let uu____5146 =
                                                FStar_ST.op_Bang sigelts  in
                                              uu____5145 :: uu____5146  in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____5142);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            (let uu____5198 =
                                               let uu____5201 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.PushOptions
                                                         (FStar_Pervasives_Native.Some
                                                            "--admit_smt_queries true")))
                                                  in
                                               let uu____5204 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____5201 :: uu____5204  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____5198);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             (let uu____5256 =
                                                let uu____5259 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       FStar_Syntax_Syntax.PopOptions)
                                                   in
                                                let uu____5260 =
                                                  FStar_ST.op_Bang sigelts
                                                   in
                                                uu____5259 :: uu____5260  in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____5256);
                                             (let uu____5309 =
                                                FStar_List.fold_left
                                                  (fun uu____5349  ->
                                                     fun action  ->
                                                       match uu____5349 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____5370 =
                                                             let uu____5377 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____5377
                                                               params_un
                                                              in
                                                           (match uu____5370
                                                            with
                                                            | (action_params,env',uu____5386)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____5412
                                                                     ->
                                                                    match uu____5412
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____5431
                                                                    =
                                                                    let uu___623_5432
                                                                    = bv  in
                                                                    let uu____5433
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___623_5432.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___623_5432.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____5433
                                                                    }  in
                                                                    (uu____5431,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____5439
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____5439
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
                                                                    uu____5478
                                                                    ->
                                                                    let uu____5479
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____5479
                                                                     in
                                                                    ((
                                                                    let uu____5483
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____5483
                                                                    then
                                                                    let uu____5488
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____5491
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____5494
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____5496
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____5488
                                                                    uu____5491
                                                                    uu____5494
                                                                    uu____5496
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
                                                                    let uu____5505
                                                                    =
                                                                    let uu____5508
                                                                    =
                                                                    let uu___645_5509
                                                                    = action
                                                                     in
                                                                    let uu____5510
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____5511
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___645_5509.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___645_5509.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___645_5509.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____5510;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____5511
                                                                    }  in
                                                                    uu____5508
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____5505))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____5309 with
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
                                                      let uu____5555 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____5562 =
                                                        let uu____5571 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____5571]  in
                                                      uu____5555 ::
                                                        uu____5562
                                                       in
                                                    let uu____5596 =
                                                      let uu____5599 =
                                                        let uu____5600 =
                                                          let uu____5601 =
                                                            let uu____5618 =
                                                              let uu____5629
                                                                =
                                                                let uu____5638
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____5641
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____5638,
                                                                  uu____5641)
                                                                 in
                                                              [uu____5629]
                                                               in
                                                            (repr,
                                                              uu____5618)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____5601
                                                           in
                                                        mk1 uu____5600  in
                                                      let uu____5677 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____5599
                                                        uu____5677
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____5596
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let uu____5678 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr2 =
                                                    register "repr" repr1  in
                                                  let uu____5682 =
                                                    let uu____5691 =
                                                      let uu____5692 =
                                                        let uu____5695 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____5695
                                                         in
                                                      uu____5692.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____5691 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____5709)
                                                        ->
                                                        let uu____5746 =
                                                          let uu____5767 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____5767
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____5835 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____5746
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____5900 =
                                                               let uu____5901
                                                                 =
                                                                 let uu____5904
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____5904
                                                                  in
                                                               uu____5901.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____5900
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____5937
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____5937
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____5952
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____5983
                                                                     ->
                                                                    match uu____5983
                                                                    with
                                                                    | 
                                                                    (bv,uu____5992)
                                                                    ->
                                                                    let uu____5997
                                                                    =
                                                                    let uu____5999
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5999
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5997
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____5952
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
                                                                    let uu____6091
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____6091
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____6101
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____6112
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____6112
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____6122
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____6125
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____6122,
                                                                    uu____6125)))
                                                              | uu____6140 ->
                                                                  let uu____6141
                                                                    =
                                                                    let uu____6147
                                                                    =
                                                                    let uu____6149
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____6149
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____6147)
                                                                     in
                                                                  raise_error1
                                                                    uu____6141))
                                                    | uu____6161 ->
                                                        let uu____6162 =
                                                          let uu____6168 =
                                                            let uu____6170 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type
                                                               in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____6170
                                                             in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____6168)
                                                           in
                                                        raise_error1
                                                          uu____6162
                                                     in
                                                  (match uu____5682 with
                                                   | (pre,post) ->
                                                       ((let uu____6203 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____6206 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____6209 =
                                                           register "wp"
                                                             wp_type
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___701_6212
                                                             = ed  in
                                                           let uu____6213 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____6214 =
                                                             let uu____6215 =
                                                               FStar_Syntax_Subst.close
                                                                 effect_binders1
                                                                 effect_signature
                                                                in
                                                             ([], uu____6215)
                                                              in
                                                           let uu____6222 =
                                                             let uu____6223 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____6223)
                                                              in
                                                           let uu____6230 =
                                                             let uu____6231 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____6231)
                                                              in
                                                           let uu____6238 =
                                                             let uu____6239 =
                                                               apply_close
                                                                 repr2
                                                                in
                                                             ([], uu____6239)
                                                              in
                                                           let uu____6246 =
                                                             let uu____6247 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____6247)
                                                              in
                                                           let uu____6254 =
                                                             let uu____6255 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____6255)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___701_6212.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___701_6212.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___701_6212.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____6213;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____6214;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____6222;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____6230;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___701_6212.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___701_6212.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___701_6212.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___701_6212.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___701_6212.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____6238;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____6246;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____6254;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___701_6212.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____6262 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____6262
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____6280
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____6280
                                                               then
                                                                 let uu____6284
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____6284
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
                                                                    let uu____6304
                                                                    =
                                                                    let uu____6307
                                                                    =
                                                                    let uu____6308
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____6308)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____6307
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
                                                                    uu____6304;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____6315
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____6315
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____6318
                                                                 =
                                                                 let uu____6321
                                                                   =
                                                                   let uu____6324
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____6324
                                                                    in
                                                                 FStar_List.append
                                                                   uu____6321
                                                                   sigelts'
                                                                  in
                                                               (uu____6318,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____6365 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____6365 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____6400 = FStar_List.hd ses  in
            uu____6400.FStar_Syntax_Syntax.sigrng  in
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
           | uu____6405 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____6411,[],t,uu____6413,uu____6414);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____6416;
               FStar_Syntax_Syntax.sigattrs = uu____6417;
               FStar_Syntax_Syntax.sigopts = uu____6418;_}::{
                                                              FStar_Syntax_Syntax.sigel
                                                                =
                                                                FStar_Syntax_Syntax.Sig_datacon
                                                                (lex_top1,uu____6420,_t_top,_lex_t_top,_6458,uu____6423);
                                                              FStar_Syntax_Syntax.sigrng
                                                                = r1;
                                                              FStar_Syntax_Syntax.sigquals
                                                                = [];
                                                              FStar_Syntax_Syntax.sigmeta
                                                                = uu____6425;
                                                              FStar_Syntax_Syntax.sigattrs
                                                                = uu____6426;
                                                              FStar_Syntax_Syntax.sigopts
                                                                = uu____6427;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____6429,_t_cons,_lex_t_cons,_6468,uu____6432);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____6434;
                 FStar_Syntax_Syntax.sigattrs = uu____6435;
                 FStar_Syntax_Syntax.sigopts = uu____6436;_}::[]
               when
               ((_6458 = Prims.int_zero) && (_6468 = Prims.int_zero)) &&
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
                 let uu____6495 =
                   let uu____6502 =
                     let uu____6503 =
                       let uu____6510 =
                         let uu____6513 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____6513
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____6510, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____6503  in
                   FStar_Syntax_Syntax.mk uu____6502  in
                 uu____6495 FStar_Pervasives_Native.None r1  in
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
                   let uu____6528 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6528
                    in
                 let hd1 =
                   let uu____6530 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6530
                    in
                 let tl1 =
                   let uu____6532 =
                     let uu____6533 =
                       let uu____6540 =
                         let uu____6541 =
                           let uu____6548 =
                             let uu____6551 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____6551
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____6548, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____6541  in
                       FStar_Syntax_Syntax.mk uu____6540  in
                     uu____6533 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6532
                    in
                 let res =
                   let uu____6557 =
                     let uu____6564 =
                       let uu____6565 =
                         let uu____6572 =
                           let uu____6575 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____6575
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____6572,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____6565  in
                     FStar_Syntax_Syntax.mk uu____6564  in
                   uu____6557 FStar_Pervasives_Native.None r2  in
                 let uu____6578 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____6578
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
               let uu____6617 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____6617;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = [];
                 FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
               }
           | uu____6622 ->
               let err_msg =
                 let uu____6627 =
                   let uu____6629 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____6629  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____6627
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
    fun uu____6654  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____6654 with
          | (uvs,t) ->
              let uu____6667 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____6667 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____6679 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____6679 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____6697 =
                        let uu____6700 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____6700
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____6697)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____6723 =
          let uu____6724 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____6724 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____6723 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____6749 =
          let uu____6750 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____6750 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____6749 r
  
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
          (let uu____6799 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____6799
           then
             let uu____6802 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____6802
           else ());
          (let uu____6807 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____6807 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____6838 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____6838 FStar_List.flatten  in
               ((let uu____6852 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____6855 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____6855)
                    in
                 if uu____6852
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
                           let uu____6871 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____6881,uu____6882,uu____6883,uu____6884,uu____6885)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____6894 -> failwith "Impossible!"  in
                           match uu____6871 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Inductive type "
                                      (Prims.op_Hat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____6913 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____6923,uu____6924,ty_lid,uu____6926,uu____6927)
                               -> (data_lid, ty_lid)
                           | uu____6934 -> failwith "Impossible"  in
                         match uu____6913 with
                         | (data_lid,ty_lid) ->
                             let uu____6942 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____6945 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____6945)
                                in
                             if uu____6942
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Exception "
                                      (Prims.op_Hat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_haseq =
                   let skip_prims_type uu____6961 =
                     let lid =
                       let ty = FStar_List.hd tcs  in
                       match ty.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_inductive_typ
                           (lid,uu____6966,uu____6967,uu____6968,uu____6969,uu____6970)
                           -> lid
                       | uu____6979 -> failwith "Impossible"  in
                     FStar_List.existsb
                       (fun s  ->
                          s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                       FStar_TypeChecker_TcInductive.early_prims_inductives
                      in
                   let is_noeq =
                     FStar_List.existsb
                       (fun q  -> q = FStar_Syntax_Syntax.Noeq) quals
                      in
                   let is_erasable uu____6996 =
                     let uu____6997 =
                       let uu____7000 = FStar_List.hd tcs  in
                       uu____7000.FStar_Syntax_Syntax.sigattrs  in
                     FStar_Syntax_Util.has_attribute uu____6997
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
          let pop1 uu____7081 =
            let uu____7082 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___885_7092  ->
               match () with
               | () ->
                   let uu____7099 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____7099 (fun r  -> pop1 (); r)) ()
          with | uu___884_7130 -> (pop1 (); FStar_Exn.raise uu___884_7130)
  
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
      | uu____7446 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____7504 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____7504 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____7529 .
    'Auu____7529 FStar_Pervasives_Native.option -> 'Auu____7529 Prims.list
  =
  fun uu___0_7538  ->
    match uu___0_7538 with
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
            let uu____7618 = collect1 tl1  in
            (match uu____7618 with
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
        | ((e,n1)::uu____7856,[]) ->
            FStar_Pervasives_Native.Some (e, n1, Prims.int_zero)
        | ([],(e,n1)::uu____7912) ->
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
          let uu____8122 =
            let uu____8124 = FStar_Options.ide ()  in
            Prims.op_Negation uu____8124  in
          if uu____8122
          then
            let uu____8127 =
              let uu____8132 = FStar_TypeChecker_Env.dsenv env  in
              let uu____8133 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____8132 uu____8133  in
            (match uu____8127 with
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
                              let uu____8166 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____8167 =
                                let uu____8173 =
                                  let uu____8175 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____8177 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____8175 uu____8177
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____8173)
                                 in
                              FStar_Errors.log_issue uu____8166 uu____8167
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____8184 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____8185 =
                                   let uu____8191 =
                                     let uu____8193 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____8193
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____8191)
                                    in
                                 FStar_Errors.log_issue uu____8184 uu____8185)
                              else ())
                         else ())))
          else ()
      | uu____8203 -> ()
  
let (unembed_optionstate_knot :
  FStar_Options.optionstate FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (unembed_optionstate :
  FStar_Syntax_Syntax.term ->
    FStar_Options.optionstate FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8233 =
      let uu____8240 =
        let uu____8243 = FStar_ST.op_Bang unembed_optionstate_knot  in
        FStar_Util.must uu____8243  in
      FStar_Syntax_Embeddings.unembed uu____8240 t  in
    uu____8233 true FStar_Syntax_Embeddings.id_norm_cb
  
let proc_check_with :
  'a . FStar_Syntax_Syntax.attribute Prims.list -> (unit -> 'a) -> 'a =
  fun attrs  ->
    fun kont  ->
      let uu____8305 =
        FStar_Syntax_Util.get_attribute FStar_Parser_Const.check_with_lid
          attrs
         in
      match uu____8305 with
      | FStar_Pervasives_Native.None  -> kont ()
      | FStar_Pervasives_Native.Some ((a,FStar_Pervasives_Native.None )::[])
          ->
          FStar_Options.with_saved_options
            (fun uu____8333  ->
               (let uu____8335 =
                  let uu____8336 = unembed_optionstate a  in
                  FStar_All.pipe_right uu____8336 FStar_Util.must  in
                FStar_Options.set uu____8335);
               kont ())
      | uu____8341 -> failwith "huh?"
  
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
        (fun uu____8392  ->
           let r = se.FStar_Syntax_Syntax.sigrng  in
           let se1 =
             let uu___1015_8395 = se  in
             let uu____8396 =
               let uu____8399 = FStar_Options.peek ()  in
               FStar_Pervasives_Native.Some uu____8399  in
             {
               FStar_Syntax_Syntax.sigel =
                 (uu___1015_8395.FStar_Syntax_Syntax.sigel);
               FStar_Syntax_Syntax.sigrng =
                 (uu___1015_8395.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___1015_8395.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___1015_8395.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___1015_8395.FStar_Syntax_Syntax.sigattrs);
               FStar_Syntax_Syntax.sigopts = uu____8396
             }  in
           match se1.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ uu____8410 ->
               failwith "Impossible bare data-constructor"
           | FStar_Syntax_Syntax.Sig_datacon uu____8438 ->
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
                         let uu___1034_8505 = e  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___1034_8505.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1034_8505.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1034_8505.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1034_8505.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (FStar_List.append
                                e.FStar_Syntax_Syntax.sigattrs
                                se1.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___1034_8505.FStar_Syntax_Syntax.sigopts)
                         }))
                  in
               let ses2 =
                 let uu____8509 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env1)
                    in
                 if uu____8509
                 then
                   let ses2 =
                     let uu____8517 =
                       let uu____8518 =
                         let uu____8519 =
                           tc_inductive
                             (let uu___1038_8528 = env1  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___1038_8528.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___1038_8528.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___1038_8528.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___1038_8528.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___1038_8528.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___1038_8528.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___1038_8528.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___1038_8528.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___1038_8528.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___1038_8528.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___1038_8528.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___1038_8528.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___1038_8528.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___1038_8528.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___1038_8528.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___1038_8528.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___1038_8528.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___1038_8528.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___1038_8528.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___1038_8528.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___1038_8528.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___1038_8528.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___1038_8528.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___1038_8528.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___1038_8528.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___1038_8528.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___1038_8528.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___1038_8528.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___1038_8528.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___1038_8528.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___1038_8528.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___1038_8528.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___1038_8528.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___1038_8528.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___1038_8528.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___1038_8528.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___1038_8528.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___1038_8528.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___1038_8528.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___1038_8528.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___1038_8528.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___1038_8528.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___1038_8528.FStar_TypeChecker_Env.erasable_types_tab)
                              }) ses1 se1.FStar_Syntax_Syntax.sigquals lids
                            in
                         FStar_All.pipe_right uu____8519
                           FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____8518
                         (FStar_TypeChecker_Normalize.elim_uvars env1)
                        in
                     FStar_All.pipe_right uu____8517
                       FStar_Syntax_Util.ses_of_sigbundle
                      in
                   ((let uu____8542 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____8542
                     then
                       let uu____8547 =
                         FStar_Syntax_Print.sigelt_to_string
                           (let uu___1042_8551 = se1  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_bundle (ses2, lids));
                              FStar_Syntax_Syntax.sigrng =
                                (uu___1042_8551.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___1042_8551.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___1042_8551.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___1042_8551.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (uu___1042_8551.FStar_Syntax_Syntax.sigopts)
                            })
                          in
                       FStar_Util.print1 "Inductive after phase 1: %s\n"
                         uu____8547
                     else ());
                    ses2)
                 else ses1  in
               let uu____8561 =
                 tc_inductive env1 ses2 se1.FStar_Syntax_Syntax.sigquals lids
                  in
               (match uu____8561 with
                | (sigbndle,projectors_ses) ->
                    let sigbndle1 =
                      let uu___1049_8585 = sigbndle  in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___1049_8585.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___1049_8585.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___1049_8585.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___1049_8585.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (se1.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___1049_8585.FStar_Syntax_Syntax.sigopts)
                      }  in
                    ([sigbndle1], projectors_ses, env0))
           | FStar_Syntax_Syntax.Sig_pragma p ->
               (FStar_Syntax_Util.process_pragma p r; ([se1], [], env0))
           | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
               let uu____8597 = cps_and_elaborate env ne  in
               (match uu____8597 with
                | (ses,ne1,lift_from_pure_opt) ->
                    let effect_and_lift_ses =
                      match lift_from_pure_opt with
                      | FStar_Pervasives_Native.Some lift ->
                          [(let uu___1063_8636 = se1  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_new_effect ne1);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___1063_8636.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___1063_8636.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___1063_8636.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___1063_8636.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (uu___1063_8636.FStar_Syntax_Syntax.sigopts)
                            });
                          lift]
                      | FStar_Pervasives_Native.None  ->
                          [(let uu___1066_8638 = se1  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_new_effect ne1);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___1066_8638.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___1066_8638.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___1066_8638.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___1066_8638.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (uu___1066_8638.FStar_Syntax_Syntax.sigopts)
                            })]
                       in
                    ([], (FStar_List.append ses effect_and_lift_ses), env0))
           | FStar_Syntax_Syntax.Sig_new_effect ne ->
               let ne1 =
                 let uu____8645 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env)
                    in
                 if uu____8645
                 then
                   let ne1 =
                     let uu____8649 =
                       let uu____8650 =
                         let uu____8651 =
                           tc_eff_decl
                             (let uu___1072_8654 = env  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___1072_8654.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___1072_8654.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___1072_8654.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___1072_8654.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___1072_8654.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___1072_8654.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___1072_8654.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___1072_8654.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___1072_8654.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___1072_8654.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___1072_8654.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___1072_8654.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___1072_8654.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___1072_8654.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___1072_8654.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___1072_8654.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___1072_8654.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___1072_8654.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___1072_8654.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___1072_8654.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___1072_8654.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___1072_8654.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___1072_8654.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___1072_8654.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___1072_8654.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___1072_8654.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___1072_8654.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___1072_8654.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___1072_8654.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___1072_8654.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___1072_8654.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___1072_8654.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___1072_8654.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___1072_8654.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___1072_8654.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___1072_8654.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___1072_8654.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___1072_8654.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___1072_8654.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___1072_8654.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___1072_8654.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___1072_8654.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___1072_8654.FStar_TypeChecker_Env.erasable_types_tab)
                              }) ne
                            in
                         FStar_All.pipe_right uu____8651
                           (fun ne1  ->
                              let uu___1075_8660 = se1  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___1075_8660.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___1075_8660.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___1075_8660.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___1075_8660.FStar_Syntax_Syntax.sigattrs);
                                FStar_Syntax_Syntax.sigopts =
                                  (uu___1075_8660.FStar_Syntax_Syntax.sigopts)
                              })
                          in
                       FStar_All.pipe_right uu____8650
                         (FStar_TypeChecker_Normalize.elim_uvars env)
                        in
                     FStar_All.pipe_right uu____8649
                       FStar_Syntax_Util.eff_decl_of_new_effect
                      in
                   ((let uu____8662 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____8662
                     then
                       let uu____8667 =
                         FStar_Syntax_Print.sigelt_to_string
                           (let uu___1079_8671 = se1  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_new_effect ne1);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___1079_8671.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___1079_8671.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___1079_8671.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___1079_8671.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (uu___1079_8671.FStar_Syntax_Syntax.sigopts)
                            })
                          in
                       FStar_Util.print1 "Effect decl after phase 1: %s\n"
                         uu____8667
                     else ());
                    ne1)
                 else ne  in
               let ne2 = tc_eff_decl env ne1  in
               let se2 =
                 let uu___1084_8679 = se1  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_new_effect ne2);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___1084_8679.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___1084_8679.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___1084_8679.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___1084_8679.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (uu___1084_8679.FStar_Syntax_Syntax.sigopts)
                 }  in
               ([se2], [], env0)
           | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
               let ed_src =
                 FStar_TypeChecker_Env.get_effect_decl env
                   sub1.FStar_Syntax_Syntax.source
                  in
               let ed_tgt =
                 FStar_TypeChecker_Env.get_effect_decl env
                   sub1.FStar_Syntax_Syntax.target
                  in
               let uu____8687 =
                 let uu____8694 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.source
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.source
                   uu____8694
                  in
               (match uu____8687 with
                | (a,wp_a_src) ->
                    let uu____8711 =
                      let uu____8718 =
                        FStar_TypeChecker_Env.lookup_effect_lid env
                          sub1.FStar_Syntax_Syntax.target
                         in
                      monad_signature env sub1.FStar_Syntax_Syntax.target
                        uu____8718
                       in
                    (match uu____8711 with
                     | (b,wp_b_tgt) ->
                         let wp_a_tgt =
                           let uu____8736 =
                             let uu____8739 =
                               let uu____8740 =
                                 let uu____8747 =
                                   FStar_Syntax_Syntax.bv_to_name a  in
                                 (b, uu____8747)  in
                               FStar_Syntax_Syntax.NT uu____8740  in
                             [uu____8739]  in
                           FStar_Syntax_Subst.subst uu____8736 wp_b_tgt  in
                         let expected_k =
                           let uu____8755 =
                             let uu____8764 = FStar_Syntax_Syntax.mk_binder a
                                in
                             let uu____8771 =
                               let uu____8780 =
                                 FStar_Syntax_Syntax.null_binder wp_a_src  in
                               [uu____8780]  in
                             uu____8764 :: uu____8771  in
                           let uu____8805 =
                             FStar_Syntax_Syntax.mk_Total wp_a_tgt  in
                           FStar_Syntax_Util.arrow uu____8755 uu____8805  in
                         let repr_type eff_name a1 wp =
                           (let uu____8827 =
                              let uu____8829 =
                                FStar_TypeChecker_Env.is_reifiable_effect env
                                  eff_name
                                 in
                              Prims.op_Negation uu____8829  in
                            if uu____8827
                            then
                              let uu____8832 =
                                let uu____8838 =
                                  FStar_Util.format1
                                    "Effect %s cannot be reified"
                                    eff_name.FStar_Ident.str
                                   in
                                (FStar_Errors.Fatal_EffectCannotBeReified,
                                  uu____8838)
                                 in
                              let uu____8842 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error uu____8832 uu____8842
                            else ());
                           (let uu____8845 =
                              FStar_TypeChecker_Env.effect_decl_opt env
                                eff_name
                               in
                            match uu____8845 with
                            | FStar_Pervasives_Native.None  ->
                                failwith
                                  "internal error: reifiable effect has no decl?"
                            | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                                let repr =
                                  FStar_TypeChecker_Env.inst_effect_fun_with
                                    [FStar_Syntax_Syntax.U_unknown] env ed
                                    ed.FStar_Syntax_Syntax.repr
                                   in
                                let uu____8878 =
                                  FStar_TypeChecker_Env.get_range env  in
                                let uu____8879 =
                                  let uu____8886 =
                                    let uu____8887 =
                                      let uu____8904 =
                                        let uu____8915 =
                                          FStar_Syntax_Syntax.as_arg a1  in
                                        let uu____8924 =
                                          let uu____8935 =
                                            FStar_Syntax_Syntax.as_arg wp  in
                                          [uu____8935]  in
                                        uu____8915 :: uu____8924  in
                                      (repr, uu____8904)  in
                                    FStar_Syntax_Syntax.Tm_app uu____8887  in
                                  FStar_Syntax_Syntax.mk uu____8886  in
                                uu____8879 FStar_Pervasives_Native.None
                                  uu____8878)
                            in
                         let uu____8980 =
                           match ((sub1.FStar_Syntax_Syntax.lift),
                                   (sub1.FStar_Syntax_Syntax.lift_wp))
                           with
                           | (FStar_Pervasives_Native.None
                              ,FStar_Pervasives_Native.None ) ->
                               failwith "Impossible (parser)"
                           | (lift,FStar_Pervasives_Native.Some
                              (uvs,lift_wp)) ->
                               let uu____9147 =
                                 if (FStar_List.length uvs) > Prims.int_zero
                                 then
                                   let uu____9158 =
                                     FStar_Syntax_Subst.univ_var_opening uvs
                                      in
                                   match uu____9158 with
                                   | (usubst,uvs1) ->
                                       let uu____9181 =
                                         FStar_TypeChecker_Env.push_univ_vars
                                           env uvs1
                                          in
                                       let uu____9182 =
                                         FStar_Syntax_Subst.subst usubst
                                           lift_wp
                                          in
                                       (uu____9181, uu____9182)
                                 else (env, lift_wp)  in
                               (match uu____9147 with
                                | (env1,lift_wp1) ->
                                    let lift_wp2 =
                                      if
                                        (FStar_List.length uvs) =
                                          Prims.int_zero
                                      then
                                        check_and_gen env1 lift_wp1
                                          expected_k
                                      else
                                        (let lift_wp2 =
                                           tc_check_trivial_guard env1
                                             lift_wp1 expected_k
                                            in
                                         let uu____9226 =
                                           FStar_Syntax_Subst.close_univ_vars
                                             uvs lift_wp2
                                            in
                                         (uvs, uu____9226))
                                       in
                                    (lift, lift_wp2))
                           | (FStar_Pervasives_Native.Some
                              (what,lift),FStar_Pervasives_Native.None ) ->
                               let uu____9291 =
                                 if (FStar_List.length what) > Prims.int_zero
                                 then
                                   let uu____9306 =
                                     FStar_Syntax_Subst.univ_var_opening what
                                      in
                                   match uu____9306 with
                                   | (usubst,uvs) ->
                                       let uu____9331 =
                                         FStar_Syntax_Subst.subst usubst lift
                                          in
                                       (uvs, uu____9331)
                                 else ([], lift)  in
                               (match uu____9291 with
                                | (uvs,lift1) ->
                                    ((let uu____9365 =
                                        FStar_TypeChecker_Env.debug env
                                          (FStar_Options.Other "ED")
                                         in
                                      if uu____9365
                                      then
                                        let uu____9369 =
                                          FStar_Syntax_Print.term_to_string
                                            lift1
                                           in
                                        FStar_Util.print1
                                          "Lift for free : %s\n" uu____9369
                                      else ());
                                     (let dmff_env =
                                        FStar_TypeChecker_DMFF.empty env
                                          (FStar_TypeChecker_TcTerm.tc_constant
                                             env FStar_Range.dummyRange)
                                         in
                                      let uu____9375 =
                                        let uu____9382 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env uvs
                                           in
                                        FStar_TypeChecker_TcTerm.tc_term
                                          uu____9382 lift1
                                         in
                                      match uu____9375 with
                                      | (lift2,comp,uu____9405) ->
                                          let uu____9406 =
                                            FStar_TypeChecker_DMFF.star_expr
                                              dmff_env lift2
                                             in
                                          (match uu____9406 with
                                           | (uu____9433,lift_wp,lift_elab)
                                               ->
                                               let lift_wp1 =
                                                 recheck_debug "lift-wp" env
                                                   lift_wp
                                                  in
                                               let lift_elab1 =
                                                 recheck_debug "lift-elab"
                                                   env lift_elab
                                                  in
                                               if
                                                 (FStar_List.length uvs) =
                                                   Prims.int_zero
                                               then
                                                 let uu____9463 =
                                                   let uu____9474 =
                                                     FStar_TypeChecker_Util.generalize_universes
                                                       env lift_elab1
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____9474
                                                    in
                                                 let uu____9491 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env lift_wp1
                                                    in
                                                 (uu____9463, uu____9491)
                                               else
                                                 (let uu____9516 =
                                                    let uu____9527 =
                                                      let uu____9536 =
                                                        FStar_Syntax_Subst.close_univ_vars
                                                          uvs lift_elab1
                                                         in
                                                      (uvs, uu____9536)  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____9527
                                                     in
                                                  let uu____9551 =
                                                    let uu____9558 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift_wp1
                                                       in
                                                    (uvs, uu____9558)  in
                                                  (uu____9516, uu____9551))))))
                            in
                         (match uu____8980 with
                          | (lift,lift_wp) ->
                              let env1 =
                                let uu___1160_9622 = env  in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1160_9622.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1160_9622.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1160_9622.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___1160_9622.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1160_9622.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___1160_9622.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1160_9622.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1160_9622.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1160_9622.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1160_9622.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___1160_9622.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1160_9622.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1160_9622.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1160_9622.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1160_9622.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1160_9622.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1160_9622.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1160_9622.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1160_9622.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1160_9622.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1160_9622.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1160_9622.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1160_9622.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1160_9622.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1160_9622.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1160_9622.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1160_9622.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1160_9622.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1160_9622.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1160_9622.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1160_9622.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1160_9622.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1160_9622.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1160_9622.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1160_9622.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1160_9622.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1160_9622.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1160_9622.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1160_9622.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1160_9622.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1160_9622.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1160_9622.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1160_9622.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1160_9622.FStar_TypeChecker_Env.erasable_types_tab)
                                }  in
                              let lift1 =
                                match lift with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Pervasives_Native.None
                                | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                    let uu____9679 =
                                      let uu____9684 =
                                        FStar_Syntax_Subst.univ_var_opening
                                          uvs
                                         in
                                      match uu____9684 with
                                      | (usubst,uvs1) ->
                                          let uu____9707 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 uvs1
                                             in
                                          let uu____9708 =
                                            FStar_Syntax_Subst.subst usubst
                                              lift1
                                             in
                                          (uu____9707, uu____9708)
                                       in
                                    (match uu____9679 with
                                     | (env2,lift2) ->
                                         let uu____9721 =
                                           let uu____9728 =
                                             FStar_TypeChecker_Env.lookup_effect_lid
                                               env2
                                               sub1.FStar_Syntax_Syntax.source
                                              in
                                           monad_signature env2
                                             sub1.FStar_Syntax_Syntax.source
                                             uu____9728
                                            in
                                         (match uu____9721 with
                                          | (a1,wp_a_src1) ->
                                              let wp_a =
                                                FStar_Syntax_Syntax.new_bv
                                                  FStar_Pervasives_Native.None
                                                  wp_a_src1
                                                 in
                                              let a_typ =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a1
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
                                                  let uu____9760 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env2
                                                     in
                                                  let uu____9761 =
                                                    let uu____9768 =
                                                      let uu____9769 =
                                                        let uu____9786 =
                                                          let uu____9797 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              a_typ
                                                             in
                                                          let uu____9806 =
                                                            let uu____9817 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                wp_a_typ
                                                               in
                                                            [uu____9817]  in
                                                          uu____9797 ::
                                                            uu____9806
                                                           in
                                                        (lift_wp1,
                                                          uu____9786)
                                                         in
                                                      FStar_Syntax_Syntax.Tm_app
                                                        uu____9769
                                                       in
                                                    FStar_Syntax_Syntax.mk
                                                      uu____9768
                                                     in
                                                  uu____9761
                                                    FStar_Pervasives_Native.None
                                                    uu____9760
                                                   in
                                                repr_type
                                                  sub1.FStar_Syntax_Syntax.target
                                                  a_typ lift_wp_a
                                                 in
                                              let expected_k1 =
                                                let uu____9865 =
                                                  let uu____9874 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a1
                                                     in
                                                  let uu____9881 =
                                                    let uu____9890 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_a
                                                       in
                                                    let uu____9897 =
                                                      let uu____9906 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          repr_f
                                                         in
                                                      [uu____9906]  in
                                                    uu____9890 :: uu____9897
                                                     in
                                                  uu____9874 :: uu____9881
                                                   in
                                                let uu____9937 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    repr_result
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____9865 uu____9937
                                                 in
                                              let uu____9940 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env2 expected_k1
                                                 in
                                              (match uu____9940 with
                                               | (expected_k2,uu____9958,uu____9959)
                                                   ->
                                                   let lift3 =
                                                     if
                                                       (FStar_List.length uvs)
                                                         = Prims.int_zero
                                                     then
                                                       check_and_gen env2
                                                         lift2 expected_k2
                                                     else
                                                       (let lift3 =
                                                          tc_check_trivial_guard
                                                            env2 lift2
                                                            expected_k2
                                                           in
                                                        let uu____9983 =
                                                          FStar_Syntax_Subst.close_univ_vars
                                                            uvs lift3
                                                           in
                                                        (uvs, uu____9983))
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     lift3)))
                                 in
                              ((let uu____9999 =
                                  let uu____10001 =
                                    let uu____10003 =
                                      FStar_All.pipe_right lift_wp
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_All.pipe_right uu____10003
                                      FStar_List.length
                                     in
                                  uu____10001 <> Prims.int_one  in
                                if uu____9999
                                then
                                  let uu____10022 =
                                    let uu____10028 =
                                      let uu____10030 =
                                        FStar_Syntax_Print.lid_to_string
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      let uu____10032 =
                                        FStar_Syntax_Print.lid_to_string
                                          sub1.FStar_Syntax_Syntax.target
                                         in
                                      let uu____10034 =
                                        let uu____10036 =
                                          let uu____10038 =
                                            FStar_All.pipe_right lift_wp
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_All.pipe_right uu____10038
                                            FStar_List.length
                                           in
                                        FStar_All.pipe_right uu____10036
                                          FStar_Util.string_of_int
                                         in
                                      FStar_Util.format3
                                        "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                        uu____10030 uu____10032 uu____10034
                                       in
                                    (FStar_Errors.Fatal_TooManyUniverse,
                                      uu____10028)
                                     in
                                  FStar_Errors.raise_error uu____10022 r
                                else ());
                               (let uu____10061 =
                                  (FStar_Util.is_some lift1) &&
                                    (let uu____10072 =
                                       let uu____10074 =
                                         let uu____10077 =
                                           FStar_All.pipe_right lift1
                                             FStar_Util.must
                                            in
                                         FStar_All.pipe_right uu____10077
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_All.pipe_right uu____10074
                                         FStar_List.length
                                        in
                                     uu____10072 <> Prims.int_one)
                                   in
                                if uu____10061
                                then
                                  let uu____10131 =
                                    let uu____10137 =
                                      let uu____10139 =
                                        FStar_Syntax_Print.lid_to_string
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      let uu____10141 =
                                        FStar_Syntax_Print.lid_to_string
                                          sub1.FStar_Syntax_Syntax.target
                                         in
                                      let uu____10143 =
                                        let uu____10145 =
                                          let uu____10147 =
                                            let uu____10150 =
                                              FStar_All.pipe_right lift1
                                                FStar_Util.must
                                               in
                                            FStar_All.pipe_right uu____10150
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_All.pipe_right uu____10147
                                            FStar_List.length
                                           in
                                        FStar_All.pipe_right uu____10145
                                          FStar_Util.string_of_int
                                         in
                                      FStar_Util.format3
                                        "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                        uu____10139 uu____10141 uu____10143
                                       in
                                    (FStar_Errors.Fatal_TooManyUniverse,
                                      uu____10137)
                                     in
                                  FStar_Errors.raise_error uu____10131 r
                                else ());
                               (let sub2 =
                                  let uu___1197_10209 = sub1  in
                                  {
                                    FStar_Syntax_Syntax.source =
                                      (uu___1197_10209.FStar_Syntax_Syntax.source);
                                    FStar_Syntax_Syntax.target =
                                      (uu___1197_10209.FStar_Syntax_Syntax.target);
                                    FStar_Syntax_Syntax.lift_wp =
                                      (FStar_Pervasives_Native.Some lift_wp);
                                    FStar_Syntax_Syntax.lift = lift1
                                  }  in
                                let se2 =
                                  let uu___1200_10211 = se1  in
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (FStar_Syntax_Syntax.Sig_sub_effect
                                         sub2);
                                    FStar_Syntax_Syntax.sigrng =
                                      (uu___1200_10211.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals =
                                      (uu___1200_10211.FStar_Syntax_Syntax.sigquals);
                                    FStar_Syntax_Syntax.sigmeta =
                                      (uu___1200_10211.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (uu___1200_10211.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (uu___1200_10211.FStar_Syntax_Syntax.sigopts)
                                  }  in
                                ([se2], [], env0))))))
           | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
               let uu____10225 =
                 if (FStar_List.length uvs) = Prims.int_zero
                 then (env, uvs, tps, c)
                 else
                   (let uu____10253 = FStar_Syntax_Subst.univ_var_opening uvs
                       in
                    match uu____10253 with
                    | (usubst,uvs1) ->
                        let tps1 =
                          FStar_Syntax_Subst.subst_binders usubst tps  in
                        let c1 =
                          let uu____10284 =
                            FStar_Syntax_Subst.shift_subst
                              (FStar_List.length tps1) usubst
                             in
                          FStar_Syntax_Subst.subst_comp uu____10284 c  in
                        let uu____10293 =
                          FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                        (uu____10293, uvs1, tps1, c1))
                  in
               (match uu____10225 with
                | (env1,uvs1,tps1,c1) ->
                    let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                    let uu____10315 = FStar_Syntax_Subst.open_comp tps1 c1
                       in
                    (match uu____10315 with
                     | (tps2,c2) ->
                         let uu____10332 =
                           FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                         (match uu____10332 with
                          | (tps3,env3,us) ->
                              let uu____10352 =
                                FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                              (match uu____10352 with
                               | (c3,u,g) ->
                                   (FStar_TypeChecker_Rel.force_trivial_guard
                                      env3 g;
                                    (let expected_result_typ =
                                       match tps3 with
                                       | (x,uu____10380)::uu____10381 ->
                                           FStar_Syntax_Syntax.bv_to_name x
                                       | uu____10400 ->
                                           FStar_Errors.raise_error
                                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                               "Effect abbreviations must bind at least the result type")
                                             r
                                        in
                                     let def_result_typ =
                                       FStar_Syntax_Util.comp_result c3  in
                                     let uu____10408 =
                                       let uu____10410 =
                                         FStar_TypeChecker_Rel.teq_nosmt_force
                                           env3 expected_result_typ
                                           def_result_typ
                                          in
                                       Prims.op_Negation uu____10410  in
                                     if uu____10408
                                     then
                                       let uu____10413 =
                                         let uu____10419 =
                                           let uu____10421 =
                                             FStar_Syntax_Print.term_to_string
                                               expected_result_typ
                                              in
                                           let uu____10423 =
                                             FStar_Syntax_Print.term_to_string
                                               def_result_typ
                                              in
                                           FStar_Util.format2
                                             "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                             uu____10421 uu____10423
                                            in
                                         (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                           uu____10419)
                                          in
                                       FStar_Errors.raise_error uu____10413 r
                                     else ());
                                    (let tps4 =
                                       FStar_Syntax_Subst.close_binders tps3
                                        in
                                     let c4 =
                                       FStar_Syntax_Subst.close_comp tps4 c3
                                        in
                                     let uu____10431 =
                                       let uu____10432 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (tps4, c4))
                                           FStar_Pervasives_Native.None r
                                          in
                                       FStar_TypeChecker_Util.generalize_universes
                                         env0 uu____10432
                                        in
                                     match uu____10431 with
                                     | (uvs2,t) ->
                                         let uu____10463 =
                                           let uu____10468 =
                                             let uu____10481 =
                                               let uu____10482 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____10482.FStar_Syntax_Syntax.n
                                                in
                                             (tps4, uu____10481)  in
                                           match uu____10468 with
                                           | ([],FStar_Syntax_Syntax.Tm_arrow
                                              (uu____10497,c5)) -> ([], c5)
                                           | (uu____10539,FStar_Syntax_Syntax.Tm_arrow
                                              (tps5,c5)) -> (tps5, c5)
                                           | uu____10578 ->
                                               failwith
                                                 "Impossible (t is an arrow)"
                                            in
                                         (match uu____10463 with
                                          | (tps5,c5) ->
                                              (if
                                                 (FStar_List.length uvs2) <>
                                                   Prims.int_one
                                               then
                                                 (let uu____10612 =
                                                    FStar_Syntax_Subst.open_univ_vars
                                                      uvs2 t
                                                     in
                                                  match uu____10612 with
                                                  | (uu____10617,t1) ->
                                                      let uu____10619 =
                                                        let uu____10625 =
                                                          let uu____10627 =
                                                            FStar_Syntax_Print.lid_to_string
                                                              lid
                                                             in
                                                          let uu____10629 =
                                                            FStar_All.pipe_right
                                                              (FStar_List.length
                                                                 uvs2)
                                                              FStar_Util.string_of_int
                                                             in
                                                          let uu____10633 =
                                                            FStar_Syntax_Print.term_to_string
                                                              t1
                                                             in
                                                          FStar_Util.format3
                                                            "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                            uu____10627
                                                            uu____10629
                                                            uu____10633
                                                           in
                                                        (FStar_Errors.Fatal_TooManyUniverse,
                                                          uu____10625)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____10619 r)
                                               else ();
                                               (let se2 =
                                                  let uu___1270_10640 = se1
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                         (lid, uvs2, tps5,
                                                           c5, flags));
                                                    FStar_Syntax_Syntax.sigrng
                                                      =
                                                      (uu___1270_10640.FStar_Syntax_Syntax.sigrng);
                                                    FStar_Syntax_Syntax.sigquals
                                                      =
                                                      (uu___1270_10640.FStar_Syntax_Syntax.sigquals);
                                                    FStar_Syntax_Syntax.sigmeta
                                                      =
                                                      (uu___1270_10640.FStar_Syntax_Syntax.sigmeta);
                                                    FStar_Syntax_Syntax.sigattrs
                                                      =
                                                      (uu___1270_10640.FStar_Syntax_Syntax.sigattrs);
                                                    FStar_Syntax_Syntax.sigopts
                                                      =
                                                      (uu___1270_10640.FStar_Syntax_Syntax.sigopts)
                                                  }  in
                                                ([se2], [], env0))))))))))
           | FStar_Syntax_Syntax.Sig_declare_typ
               (uu____10647,uu____10648,uu____10649) when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___1_10654  ->
                       match uu___1_10654 with
                       | FStar_Syntax_Syntax.OnlyName  -> true
                       | uu____10657 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_let (uu____10663,uu____10664) when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___1_10673  ->
                       match uu___1_10673 with
                       | FStar_Syntax_Syntax.OnlyName  -> true
                       | uu____10676 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
               let env1 = FStar_TypeChecker_Env.set_range env r  in
               ((let uu____10687 = FStar_TypeChecker_Env.lid_exists env1 lid
                    in
                 if uu____10687
                 then
                   let uu____10690 =
                     let uu____10696 =
                       let uu____10698 = FStar_Ident.text_of_lid lid  in
                       FStar_Util.format1
                         "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                         uu____10698
                        in
                     (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                       uu____10696)
                      in
                   FStar_Errors.raise_error uu____10690 r
                 else ());
                (let uu____10704 =
                   let uu____10713 =
                     (FStar_Options.use_two_phase_tc ()) &&
                       (FStar_TypeChecker_Env.should_verify env1)
                      in
                   if uu____10713
                   then
                     let uu____10724 =
                       tc_declare_typ
                         (let uu___1294_10727 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1294_10727.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1294_10727.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1294_10727.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1294_10727.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1294_10727.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1294_10727.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1294_10727.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1294_10727.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1294_10727.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1294_10727.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1294_10727.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1294_10727.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1294_10727.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1294_10727.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1294_10727.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1294_10727.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1294_10727.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1294_10727.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1294_10727.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1294_10727.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1294_10727.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___1294_10727.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___1294_10727.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1294_10727.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1294_10727.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1294_10727.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1294_10727.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1294_10727.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1294_10727.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1294_10727.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1294_10727.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1294_10727.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1294_10727.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1294_10727.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1294_10727.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1294_10727.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1294_10727.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1294_10727.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1294_10727.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1294_10727.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1294_10727.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1294_10727.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1294_10727.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___1294_10727.FStar_TypeChecker_Env.erasable_types_tab)
                          }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng
                        in
                     match uu____10724 with
                     | (uvs1,t1) ->
                         ((let uu____10752 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "TwoPhases")
                              in
                           if uu____10752
                           then
                             let uu____10757 =
                               FStar_Syntax_Print.term_to_string t1  in
                             let uu____10759 =
                               FStar_Syntax_Print.univ_names_to_string uvs1
                                in
                             FStar_Util.print2
                               "Val declaration after phase 1: %s and uvs: %s\n"
                               uu____10757 uu____10759
                           else ());
                          (uvs1, t1))
                   else (uvs, t)  in
                 match uu____10704 with
                 | (uvs1,t1) ->
                     let uu____10794 =
                       tc_declare_typ env1 (uvs1, t1)
                         se1.FStar_Syntax_Syntax.sigrng
                        in
                     (match uu____10794 with
                      | (uvs2,t2) ->
                          ([(let uu___1307_10824 = se1  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (lid, uvs2, t2));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___1307_10824.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___1307_10824.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___1307_10824.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___1307_10824.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___1307_10824.FStar_Syntax_Syntax.sigopts)
                             })], [], env0))))
           | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
               let env1 = FStar_TypeChecker_Env.set_range env r  in
               let uu____10829 =
                 let uu____10838 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env1)
                    in
                 if uu____10838
                 then
                   let uu____10849 =
                     tc_assume
                       (let uu___1316_10852 = env1  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___1316_10852.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___1316_10852.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___1316_10852.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___1316_10852.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___1316_10852.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___1316_10852.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___1316_10852.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___1316_10852.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___1316_10852.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___1316_10852.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___1316_10852.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___1316_10852.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___1316_10852.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___1316_10852.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___1316_10852.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level =
                            (uu___1316_10852.FStar_TypeChecker_Env.top_level);
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___1316_10852.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___1316_10852.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___1316_10852.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___1316_10852.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax = true;
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___1316_10852.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 = true;
                          FStar_TypeChecker_Env.failhard =
                            (uu___1316_10852.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___1316_10852.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___1316_10852.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___1316_10852.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___1316_10852.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___1316_10852.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___1316_10852.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___1316_10852.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___1316_10852.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___1316_10852.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___1316_10852.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___1316_10852.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___1316_10852.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___1316_10852.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___1316_10852.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___1316_10852.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___1316_10852.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___1316_10852.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___1316_10852.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___1316_10852.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___1316_10852.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (uu___1316_10852.FStar_TypeChecker_Env.erasable_types_tab)
                        }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng
                      in
                   match uu____10849 with
                   | (uvs1,t1) ->
                       ((let uu____10878 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "TwoPhases")
                            in
                         if uu____10878
                         then
                           let uu____10883 =
                             FStar_Syntax_Print.term_to_string t1  in
                           let uu____10885 =
                             FStar_Syntax_Print.univ_names_to_string uvs1  in
                           FStar_Util.print2
                             "Assume after phase 1: %s and uvs: %s\n"
                             uu____10883 uu____10885
                         else ());
                        (uvs1, t1))
                 else (uvs, t)  in
               (match uu____10829 with
                | (uvs1,t1) ->
                    let uu____10920 =
                      tc_assume env1 (uvs1, t1)
                        se1.FStar_Syntax_Syntax.sigrng
                       in
                    (match uu____10920 with
                     | (uvs2,t2) ->
                         ([(let uu___1329_10950 = se1  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_assume
                                   (lid, uvs2, t2));
                              FStar_Syntax_Syntax.sigrng =
                                (uu___1329_10950.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___1329_10950.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___1329_10950.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___1329_10950.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (uu___1329_10950.FStar_Syntax_Syntax.sigopts)
                            })], [], env0)))
           | FStar_Syntax_Syntax.Sig_main e ->
               let env1 = FStar_TypeChecker_Env.set_range env r  in
               let env2 =
                 FStar_TypeChecker_Env.set_expected_typ env1
                   FStar_Syntax_Syntax.t_unit
                  in
               let uu____10954 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
               (match uu____10954 with
                | (e1,c,g1) ->
                    let uu____10974 =
                      let uu____10981 =
                        let uu____10984 =
                          FStar_Syntax_Util.ml_comp
                            FStar_Syntax_Syntax.t_unit r
                           in
                        FStar_Pervasives_Native.Some uu____10984  in
                      let uu____10985 =
                        let uu____10990 = FStar_Syntax_Syntax.lcomp_comp c
                           in
                        (e1, uu____10990)  in
                      FStar_TypeChecker_TcTerm.check_expected_effect env2
                        uu____10981 uu____10985
                       in
                    (match uu____10974 with
                     | (e2,uu____11002,g) ->
                         ((let uu____11005 =
                             FStar_TypeChecker_Env.conj_guard g1 g  in
                           FStar_TypeChecker_Rel.force_trivial_guard env2
                             uu____11005);
                          (let se2 =
                             let uu___1344_11007 = se1  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_main e2);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___1344_11007.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___1344_11007.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___1344_11007.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___1344_11007.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___1344_11007.FStar_Syntax_Syntax.sigopts)
                             }  in
                           ([se2], [], env0)))))
           | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
               ((let uu____11019 = FStar_Options.debug_any ()  in
                 if uu____11019
                 then
                   let uu____11022 =
                     FStar_Ident.string_of_lid
                       env.FStar_TypeChecker_Env.curmodule
                      in
                   let uu____11024 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print2 "%s: Found splice of (%s)\n" uu____11022
                     uu____11024
                 else ());
                (let uu____11029 = FStar_TypeChecker_TcTerm.tc_tactic env t
                    in
                 match uu____11029 with
                 | (t1,uu____11047,g) ->
                     (FStar_TypeChecker_Rel.force_trivial_guard env g;
                      (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                       let lids' =
                         FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                           ses
                          in
                       FStar_List.iter
                         (fun lid  ->
                            let uu____11061 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids'
                               in
                            match uu____11061 with
                            | FStar_Pervasives_Native.None  when
                                Prims.op_Negation
                                  env.FStar_TypeChecker_Env.nosynth
                                ->
                                let uu____11064 =
                                  let uu____11070 =
                                    let uu____11072 =
                                      FStar_Ident.string_of_lid lid  in
                                    let uu____11074 =
                                      let uu____11076 =
                                        FStar_List.map
                                          FStar_Ident.string_of_lid lids'
                                         in
                                      FStar_All.pipe_left
                                        (FStar_String.concat ", ")
                                        uu____11076
                                       in
                                    FStar_Util.format2
                                      "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                      uu____11072 uu____11074
                                     in
                                  (FStar_Errors.Fatal_SplicedUndef,
                                    uu____11070)
                                   in
                                FStar_Errors.raise_error uu____11064 r
                            | uu____11088 -> ()) lids;
                       (let dsenv1 =
                          FStar_List.fold_left
                            FStar_Syntax_DsEnv.push_sigelt_force
                            env.FStar_TypeChecker_Env.dsenv ses
                           in
                        let env1 =
                          let uu___1365_11093 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1365_11093.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1365_11093.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1365_11093.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1365_11093.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1365_11093.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1365_11093.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1365_11093.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1365_11093.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1365_11093.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1365_11093.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1365_11093.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1365_11093.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1365_11093.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1365_11093.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1365_11093.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1365_11093.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1365_11093.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1365_11093.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1365_11093.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1365_11093.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___1365_11093.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1365_11093.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___1365_11093.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___1365_11093.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1365_11093.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1365_11093.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1365_11093.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1365_11093.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1365_11093.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1365_11093.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1365_11093.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1365_11093.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1365_11093.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1365_11093.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1365_11093.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1365_11093.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1365_11093.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1365_11093.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1365_11093.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1365_11093.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1365_11093.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv = dsenv1;
                            FStar_TypeChecker_Env.nbe =
                              (uu___1365_11093.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1365_11093.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___1365_11093.FStar_TypeChecker_Env.erasable_types_tab)
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
                     let uu____11161 =
                       let uu____11163 =
                         let uu____11172 = drop_logic val_q  in
                         let uu____11175 = drop_logic q'  in
                         (uu____11172, uu____11175)  in
                       match uu____11163 with
                       | (val_q1,q'1) ->
                           ((FStar_List.length val_q1) =
                              (FStar_List.length q'1))
                             &&
                             (FStar_List.forall2
                                FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                        in
                     if uu____11161
                     then FStar_Pervasives_Native.Some q'
                     else
                       (let uu____11202 =
                          let uu____11208 =
                            let uu____11210 =
                              FStar_Syntax_Print.lid_to_string l  in
                            let uu____11212 =
                              FStar_Syntax_Print.quals_to_string val_q  in
                            let uu____11214 =
                              FStar_Syntax_Print.quals_to_string q'  in
                            FStar_Util.format3
                              "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                              uu____11210 uu____11212 uu____11214
                             in
                          (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                            uu____11208)
                           in
                        FStar_Errors.raise_error uu____11202 r)
                  in
               let rename_parameters lb =
                 let rename_in_typ def typ =
                   let typ1 = FStar_Syntax_Subst.compress typ  in
                   let def_bs =
                     let uu____11251 =
                       let uu____11252 = FStar_Syntax_Subst.compress def  in
                       uu____11252.FStar_Syntax_Syntax.n  in
                     match uu____11251 with
                     | FStar_Syntax_Syntax.Tm_abs
                         (binders,uu____11264,uu____11265) -> binders
                     | uu____11290 -> []  in
                   match typ1 with
                   | {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                         (val_bs,c);
                       FStar_Syntax_Syntax.pos = r1;
                       FStar_Syntax_Syntax.vars = uu____11302;_} ->
                       let has_auto_name bv =
                         FStar_Util.starts_with
                           (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                           FStar_Ident.reserved_prefix
                          in
                       let rec rename_binders1 def_bs1 val_bs1 =
                         match (def_bs1, val_bs1) with
                         | ([],uu____11407) -> val_bs1
                         | (uu____11438,[]) -> val_bs1
                         | ((body_bv,uu____11470)::bt,(val_bv,aqual)::vt) ->
                             let uu____11527 = rename_binders1 bt vt  in
                             ((match ((has_auto_name body_bv),
                                       (has_auto_name val_bv))
                               with
                               | (true ,uu____11551) -> (val_bv, aqual)
                               | (false ,true ) ->
                                   ((let uu___1434_11565 = val_bv  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (let uu___1436_11568 =
                                            val_bv.FStar_Syntax_Syntax.ppname
                                             in
                                          {
                                            FStar_Ident.idText =
                                              ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                            FStar_Ident.idRange =
                                              (uu___1436_11568.FStar_Ident.idRange)
                                          });
                                       FStar_Syntax_Syntax.index =
                                         (uu___1434_11565.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (uu___1434_11565.FStar_Syntax_Syntax.sort)
                                     }), aqual)
                               | (false ,false ) -> (val_bv, aqual))) ::
                               uu____11527
                          in
                       let uu____11575 =
                         let uu____11582 =
                           let uu____11583 =
                             let uu____11598 = rename_binders1 def_bs val_bs
                                in
                             (uu____11598, c)  in
                           FStar_Syntax_Syntax.Tm_arrow uu____11583  in
                         FStar_Syntax_Syntax.mk uu____11582  in
                       uu____11575 FStar_Pervasives_Native.None r1
                   | uu____11617 -> typ1  in
                 let uu___1442_11618 = lb  in
                 let uu____11619 =
                   rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                     lb.FStar_Syntax_Syntax.lbtyp
                    in
                 {
                   FStar_Syntax_Syntax.lbname =
                     (uu___1442_11618.FStar_Syntax_Syntax.lbname);
                   FStar_Syntax_Syntax.lbunivs =
                     (uu___1442_11618.FStar_Syntax_Syntax.lbunivs);
                   FStar_Syntax_Syntax.lbtyp = uu____11619;
                   FStar_Syntax_Syntax.lbeff =
                     (uu___1442_11618.FStar_Syntax_Syntax.lbeff);
                   FStar_Syntax_Syntax.lbdef =
                     (uu___1442_11618.FStar_Syntax_Syntax.lbdef);
                   FStar_Syntax_Syntax.lbattrs =
                     (uu___1442_11618.FStar_Syntax_Syntax.lbattrs);
                   FStar_Syntax_Syntax.lbpos =
                     (uu___1442_11618.FStar_Syntax_Syntax.lbpos)
                 }  in
               let uu____11622 =
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.fold_left
                      (fun uu____11677  ->
                         fun lb  ->
                           match uu____11677 with
                           | (gen1,lbs1,quals_opt) ->
                               let lbname =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu____11723 =
                                 let uu____11735 =
                                   FStar_TypeChecker_Env.try_lookup_val_decl
                                     env1
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 match uu____11735 with
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
                                       | uu____11815 ->
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
                                      (let uu____11862 =
                                         FStar_Syntax_Syntax.mk_lb
                                           ((FStar_Util.Inr lbname), uvs,
                                             FStar_Parser_Const.effect_ALL_lid,
                                             tval, def, [],
                                             (lb.FStar_Syntax_Syntax.lbpos))
                                          in
                                       (false, uu____11862, quals_opt1)))
                                  in
                               (match uu____11723 with
                                | (gen2,lb1,quals_opt1) ->
                                    (gen2, (lb1 :: lbs1), quals_opt1)))
                      (true, [],
                        (if se1.FStar_Syntax_Syntax.sigquals = []
                         then FStar_Pervasives_Native.None
                         else
                           FStar_Pervasives_Native.Some
                             (se1.FStar_Syntax_Syntax.sigquals))))
                  in
               (match uu____11622 with
                | (should_generalize,lbs',quals_opt) ->
                    let quals =
                      match quals_opt with
                      | FStar_Pervasives_Native.None  ->
                          [FStar_Syntax_Syntax.Visible_default]
                      | FStar_Pervasives_Native.Some q ->
                          let uu____11966 =
                            FStar_All.pipe_right q
                              (FStar_Util.for_some
                                 (fun uu___2_11972  ->
                                    match uu___2_11972 with
                                    | FStar_Syntax_Syntax.Irreducible  ->
                                        true
                                    | FStar_Syntax_Syntax.Visible_default  ->
                                        true
                                    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                         -> true
                                    | uu____11977 -> false))
                             in
                          if uu____11966
                          then q
                          else FStar_Syntax_Syntax.Visible_default :: q
                       in
                    let lbs'1 = FStar_List.rev lbs'  in
                    let e =
                      let uu____11990 =
                        let uu____11997 =
                          let uu____11998 =
                            let uu____12012 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   FStar_Const.Const_unit)
                                FStar_Pervasives_Native.None r
                               in
                            (((FStar_Pervasives_Native.fst lbs), lbs'1),
                              uu____12012)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____11998  in
                        FStar_Syntax_Syntax.mk uu____11997  in
                      uu____11990 FStar_Pervasives_Native.None r  in
                    let env' =
                      let uu___1485_12031 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1485_12031.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1485_12031.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1485_12031.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1485_12031.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1485_12031.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1485_12031.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1485_12031.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1485_12031.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1485_12031.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1485_12031.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1485_12031.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1485_12031.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1485_12031.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize = should_generalize;
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1485_12031.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level = true;
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1485_12031.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1485_12031.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1485_12031.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1485_12031.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___1485_12031.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1485_12031.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1485_12031.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1485_12031.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1485_12031.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1485_12031.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1485_12031.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1485_12031.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1485_12031.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1485_12031.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1485_12031.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1485_12031.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1485_12031.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1485_12031.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1485_12031.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1485_12031.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1485_12031.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1485_12031.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1485_12031.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1485_12031.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1485_12031.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___1485_12031.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___1485_12031.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1485_12031.FStar_TypeChecker_Env.strict_args_tab);
                        FStar_TypeChecker_Env.erasable_types_tab =
                          (uu___1485_12031.FStar_TypeChecker_Env.erasable_types_tab)
                      }  in
                    let e1 =
                      let uu____12034 =
                        (FStar_Options.use_two_phase_tc ()) &&
                          (FStar_TypeChecker_Env.should_verify env')
                         in
                      if uu____12034
                      then
                        let drop_lbtyp e_lax =
                          let uu____12043 =
                            let uu____12044 =
                              FStar_Syntax_Subst.compress e_lax  in
                            uu____12044.FStar_Syntax_Syntax.n  in
                          match uu____12043 with
                          | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2)
                              ->
                              let lb_unannotated =
                                let uu____12066 =
                                  let uu____12067 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____12067.FStar_Syntax_Syntax.n  in
                                match uu____12066 with
                                | FStar_Syntax_Syntax.Tm_let
                                    ((uu____12071,lb1::[]),uu____12073) ->
                                    let uu____12089 =
                                      let uu____12090 =
                                        FStar_Syntax_Subst.compress
                                          lb1.FStar_Syntax_Syntax.lbtyp
                                         in
                                      uu____12090.FStar_Syntax_Syntax.n  in
                                    (match uu____12089 with
                                     | FStar_Syntax_Syntax.Tm_unknown  ->
                                         true
                                     | uu____12095 -> false)
                                | uu____12097 ->
                                    failwith
                                      "Impossible: first phase lb and second phase lb differ in structure!"
                                 in
                              if lb_unannotated
                              then
                                let uu___1510_12101 = e_lax  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_let
                                       ((false,
                                          [(let uu___1512_12116 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___1512_12116.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___1512_12116.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                FStar_Syntax_Syntax.tun;
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___1512_12116.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___1512_12116.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___1512_12116.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___1512_12116.FStar_Syntax_Syntax.lbpos)
                                            })]), e2));
                                  FStar_Syntax_Syntax.pos =
                                    (uu___1510_12101.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1510_12101.FStar_Syntax_Syntax.vars)
                                }
                              else e_lax
                          | uu____12119 -> e_lax  in
                        let uu____12120 =
                          FStar_Util.record_time
                            (fun uu____12128  ->
                               let uu____12129 =
                                 let uu____12130 =
                                   let uu____12131 =
                                     FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                       (let uu___1516_12140 = env'  in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___1516_12140.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___1516_12140.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___1516_12140.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___1516_12140.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___1516_12140.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___1516_12140.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___1516_12140.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___1516_12140.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___1516_12140.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___1516_12140.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.is_pattern =
                                            (uu___1516_12140.FStar_TypeChecker_Env.is_pattern);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___1516_12140.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___1516_12140.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___1516_12140.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___1516_12140.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___1516_12140.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___1516_12140.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            (uu___1516_12140.FStar_TypeChecker_Env.use_eq);
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___1516_12140.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___1516_12140.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax = true;
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___1516_12140.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 = true;
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___1516_12140.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___1516_12140.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___1516_12140.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___1516_12140.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___1516_12140.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___1516_12140.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___1516_12140.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___1516_12140.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___1516_12140.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___1516_12140.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___1516_12140.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___1516_12140.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___1516_12140.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___1516_12140.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___1516_12140.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.is_native_tactic
                                            =
                                            (uu___1516_12140.FStar_TypeChecker_Env.is_native_tactic);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___1516_12140.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___1516_12140.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___1516_12140.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___1516_12140.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___1516_12140.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (uu___1516_12140.FStar_TypeChecker_Env.erasable_types_tab)
                                        }) e
                                      in
                                   FStar_All.pipe_right uu____12131
                                     (fun uu____12153  ->
                                        match uu____12153 with
                                        | (e1,uu____12161,uu____12162) -> e1)
                                    in
                                 FStar_All.pipe_right uu____12130
                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                      env')
                                  in
                               FStar_All.pipe_right uu____12129 drop_lbtyp)
                           in
                        match uu____12120 with
                        | (e1,ms) ->
                            ((let uu____12168 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "TwoPhases")
                                 in
                              if uu____12168
                              then
                                let uu____12173 =
                                  FStar_Syntax_Print.term_to_string e1  in
                                FStar_Util.print1
                                  "Let binding after phase 1: %s\n"
                                  uu____12173
                              else ());
                             (let uu____12179 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "TCDeclTime")
                                 in
                              if uu____12179
                              then
                                let uu____12184 = FStar_Util.string_of_int ms
                                   in
                                FStar_Util.print1
                                  "Let binding elaborated (phase 1) in %s milliseconds\n"
                                  uu____12184
                              else ());
                             e1)
                      else e  in
                    let uu____12191 =
                      let uu____12200 =
                        FStar_Syntax_Util.extract_attr'
                          FStar_Parser_Const.postprocess_with
                          se1.FStar_Syntax_Syntax.sigattrs
                         in
                      match uu____12200 with
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
                    (match uu____12191 with
                     | (attrs,post_tau) ->
                         let se2 =
                           let uu___1546_12305 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___1546_12305.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1546_12305.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___1546_12305.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1546_12305.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs = attrs;
                             FStar_Syntax_Syntax.sigopts =
                               (uu___1546_12305.FStar_Syntax_Syntax.sigopts)
                           }  in
                         let postprocess_lb tau lb =
                           let lbdef =
                             env1.FStar_TypeChecker_Env.postprocess env1 tau
                               lb.FStar_Syntax_Syntax.lbtyp
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           let uu___1553_12318 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___1553_12318.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___1553_12318.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___1553_12318.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___1553_12318.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = lbdef;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___1553_12318.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___1553_12318.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let uu____12319 =
                           FStar_Util.record_time
                             (fun uu____12338  ->
                                FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                  env' e1)
                            in
                         (match uu____12319 with
                          | (r1,ms) ->
                              ((let uu____12366 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env1)
                                    (FStar_Options.Other "TCDeclTime")
                                   in
                                if uu____12366
                                then
                                  let uu____12371 =
                                    FStar_Util.string_of_int ms  in
                                  FStar_Util.print1
                                    "Let binding typechecked in phase 2 in %s milliseconds\n"
                                    uu____12371
                                else ());
                               (let uu____12376 =
                                  match r1 with
                                  | ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                                       FStar_Syntax_Syntax.pos = uu____12401;
                                       FStar_Syntax_Syntax.vars = uu____12402;_},uu____12403,g)
                                      when FStar_TypeChecker_Env.is_trivial g
                                      ->
                                      let lbs2 =
                                        let uu____12433 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.snd lbs1)
                                            (FStar_List.map rename_parameters)
                                           in
                                        ((FStar_Pervasives_Native.fst lbs1),
                                          uu____12433)
                                         in
                                      let lbs3 =
                                        let uu____12457 =
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
                                          uu____12457)
                                         in
                                      let quals1 =
                                        match e2.FStar_Syntax_Syntax.n with
                                        | FStar_Syntax_Syntax.Tm_meta
                                            (uu____12480,FStar_Syntax_Syntax.Meta_desugared
                                             (FStar_Syntax_Syntax.Masked_effect
                                             ))
                                            ->
                                            FStar_Syntax_Syntax.HasMaskedEffect
                                            :: quals
                                        | uu____12485 -> quals  in
                                      ((let uu___1583_12494 = se2  in
                                        {
                                          FStar_Syntax_Syntax.sigel =
                                            (FStar_Syntax_Syntax.Sig_let
                                               (lbs3, lids));
                                          FStar_Syntax_Syntax.sigrng =
                                            (uu___1583_12494.FStar_Syntax_Syntax.sigrng);
                                          FStar_Syntax_Syntax.sigquals =
                                            quals1;
                                          FStar_Syntax_Syntax.sigmeta =
                                            (uu___1583_12494.FStar_Syntax_Syntax.sigmeta);
                                          FStar_Syntax_Syntax.sigattrs =
                                            (uu___1583_12494.FStar_Syntax_Syntax.sigattrs);
                                          FStar_Syntax_Syntax.sigopts =
                                            (uu___1583_12494.FStar_Syntax_Syntax.sigopts)
                                        }), lbs3)
                                  | uu____12497 ->
                                      failwith
                                        "impossible (typechecking should preserve Tm_let)"
                                   in
                                match uu____12376 with
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
                                     (let uu____12553 = log env1  in
                                      if uu____12553
                                      then
                                        let uu____12556 =
                                          let uu____12558 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.snd
                                                 lbs1)
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let should_log =
                                                      let uu____12578 =
                                                        let uu____12587 =
                                                          let uu____12588 =
                                                            let uu____12591 =
                                                              FStar_Util.right
                                                                lb.FStar_Syntax_Syntax.lbname
                                                               in
                                                            uu____12591.FStar_Syntax_Syntax.fv_name
                                                             in
                                                          uu____12588.FStar_Syntax_Syntax.v
                                                           in
                                                        FStar_TypeChecker_Env.try_lookup_val_decl
                                                          env1 uu____12587
                                                         in
                                                      match uu____12578 with
                                                      | FStar_Pervasives_Native.None
                                                           -> true
                                                      | uu____12600 -> false
                                                       in
                                                    if should_log
                                                    then
                                                      let uu____12612 =
                                                        FStar_Syntax_Print.lbname_to_string
                                                          lb.FStar_Syntax_Syntax.lbname
                                                         in
                                                      let uu____12614 =
                                                        FStar_Syntax_Print.term_to_string
                                                          lb.FStar_Syntax_Syntax.lbtyp
                                                         in
                                                      FStar_Util.format2
                                                        "let %s : %s"
                                                        uu____12612
                                                        uu____12614
                                                    else ""))
                                             in
                                          FStar_All.pipe_right uu____12558
                                            (FStar_String.concat "\n")
                                           in
                                        FStar_Util.print1 "%s\n" uu____12556
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
      (let uu____12666 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____12666
       then
         let uu____12669 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____12669
       else ());
      (let uu____12674 = get_fail_se se  in
       match uu____12674 with
       | FStar_Pervasives_Native.Some (uu____12695,false ) when
           let uu____12712 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____12712 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___1614_12738 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___1614_12738.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___1614_12738.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___1614_12738.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___1614_12738.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___1614_12738.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___1614_12738.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___1614_12738.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___1614_12738.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___1614_12738.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___1614_12738.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___1614_12738.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___1614_12738.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___1614_12738.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___1614_12738.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___1614_12738.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___1614_12738.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___1614_12738.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___1614_12738.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___1614_12738.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___1614_12738.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___1614_12738.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___1614_12738.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___1614_12738.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___1614_12738.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___1614_12738.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___1614_12738.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___1614_12738.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___1614_12738.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___1614_12738.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___1614_12738.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___1614_12738.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___1614_12738.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___1614_12738.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___1614_12738.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___1614_12738.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___1614_12738.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___1614_12738.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___1614_12738.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___1614_12738.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___1614_12738.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___1614_12738.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___1614_12738.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___1614_12738.FStar_TypeChecker_Env.strict_args_tab);
                 FStar_TypeChecker_Env.erasable_types_tab =
                   (uu___1614_12738.FStar_TypeChecker_Env.erasable_types_tab)
               }
             else env1  in
           ((let uu____12743 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____12743
             then
               let uu____12746 =
                 let uu____12748 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____12748
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____12746
             else ());
            (let uu____12762 =
               FStar_Errors.catch_errors
                 (fun uu____12792  ->
                    FStar_Options.with_saved_options
                      (fun uu____12804  -> tc_decl' env' se))
                in
             match uu____12762 with
             | (errs,uu____12816) ->
                 ((let uu____12846 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____12846
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____12881 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____12881  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____12893 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____12904 =
                            let uu____12914 = check_multi_eq errnos1 actual
                               in
                            match uu____12914 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- Prims.int_one), (~- Prims.int_one),
                                  (~- Prims.int_one))
                             in
                          (match uu____12904 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____12979 =
                                   let uu____12985 =
                                     let uu____12987 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____12990 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____12993 =
                                       FStar_Util.string_of_int e  in
                                     let uu____12995 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____12997 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____12987 uu____12990 uu____12993
                                       uu____12995 uu____12997
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____12985)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____12979)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____13024 .
    'Auu____13024 ->
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
               (fun uu___3_13067  ->
                  match uu___3_13067 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____13070 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____13081) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____13089 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____13099 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____13104 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____13120 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____13146 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13172) ->
            let uu____13181 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13181
            then
              let for_export_bundle se1 uu____13218 =
                match uu____13218 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____13257,uu____13258) ->
                         let dec =
                           let uu___1690_13268 = se1  in
                           let uu____13269 =
                             let uu____13270 =
                               let uu____13277 =
                                 let uu____13278 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____13278  in
                               (l, us, uu____13277)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____13270
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____13269;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1690_13268.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1690_13268.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1690_13268.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___1690_13268.FStar_Syntax_Syntax.sigopts)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____13288,uu____13289,uu____13290) ->
                         let dec =
                           let uu___1701_13298 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1701_13298.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1701_13298.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1701_13298.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___1701_13298.FStar_Syntax_Syntax.sigopts)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____13303 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____13326,uu____13327,uu____13328) ->
            let uu____13329 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13329 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____13353 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____13353
            then
              ([(let uu___1717_13372 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___1717_13372.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___1717_13372.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___1717_13372.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (uu___1717_13372.FStar_Syntax_Syntax.sigopts)
                 })], (l :: hidden))
            else
              (let uu____13375 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_13381  ->
                         match uu___4_13381 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____13384 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____13390 ->
                             true
                         | uu____13392 -> false))
                  in
               if uu____13375 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____13413 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____13418 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13423 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____13428 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13433 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13451) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____13465 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____13465
            then ([], hidden)
            else
              (let dec =
                 let uu____13486 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____13486;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = [];
                   FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____13497 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13497
            then
              let uu____13508 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1754_13522 = se  in
                        let uu____13523 =
                          let uu____13524 =
                            let uu____13531 =
                              let uu____13532 =
                                let uu____13535 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____13535.FStar_Syntax_Syntax.fv_name  in
                              uu____13532.FStar_Syntax_Syntax.v  in
                            (uu____13531, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____13524  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____13523;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1754_13522.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1754_13522.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1754_13522.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___1754_13522.FStar_Syntax_Syntax.sigopts)
                        }))
                 in
              (uu____13508, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> Prims.bool -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      fun from_cache  ->
        (let uu____13565 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____13565
         then
           let uu____13568 = FStar_Syntax_Print.sigelt_to_string se  in
           let uu____13570 = FStar_Util.string_of_bool from_cache  in
           FStar_Util.print2
             ">>>>>>>>>>>>>>Adding top-level decl to environment: %s (from_cache:%s)\n"
             uu____13568 uu____13570
         else ());
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____13575 ->
             let uu____13592 =
               let uu____13598 =
                 let uu____13600 = FStar_Syntax_Print.sigelt_to_string se  in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____13600
                  in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____13598)  in
             FStar_Errors.raise_error uu____13592
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_datacon uu____13604 ->
             let uu____13620 =
               let uu____13626 =
                 let uu____13628 = FStar_Syntax_Print.sigelt_to_string se  in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____13628
                  in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____13626)  in
             FStar_Errors.raise_error uu____13620
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_declare_typ
             (uu____13632,uu____13633,uu____13634) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___5_13639  ->
                     match uu___5_13639 with
                     | FStar_Syntax_Syntax.OnlyName  -> true
                     | uu____13642 -> false))
             -> env
         | FStar_Syntax_Syntax.Sig_let (uu____13644,uu____13645) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___5_13654  ->
                     match uu___5_13654 with
                     | FStar_Syntax_Syntax.OnlyName  -> true
                     | uu____13657 -> false))
             -> env
         | uu____13659 ->
             let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PushOptions uu____13661) ->
                  if from_cache
                  then env1
                  else
                    (let uu___1791_13668 = env1  in
                     let uu____13669 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___1791_13668.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___1791_13668.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___1791_13668.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___1791_13668.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___1791_13668.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___1791_13668.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___1791_13668.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___1791_13668.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___1791_13668.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___1791_13668.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___1791_13668.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___1791_13668.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___1791_13668.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___1791_13668.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___1791_13668.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___1791_13668.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___1791_13668.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___1791_13668.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___1791_13668.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___1791_13668.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___1791_13668.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___1791_13668.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___1791_13668.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___1791_13668.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___1791_13668.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___1791_13668.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___1791_13668.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___1791_13668.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___1791_13668.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___1791_13668.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___1791_13668.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___1791_13668.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___1791_13668.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___1791_13668.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____13669;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___1791_13668.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___1791_13668.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___1791_13668.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___1791_13668.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___1791_13668.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___1791_13668.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___1791_13668.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___1791_13668.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___1791_13668.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___1791_13668.FStar_TypeChecker_Env.erasable_types_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PopOptions ) ->
                  if from_cache
                  then env1
                  else
                    (let uu___1791_13673 = env1  in
                     let uu____13674 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___1791_13673.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___1791_13673.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___1791_13673.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___1791_13673.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___1791_13673.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___1791_13673.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___1791_13673.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___1791_13673.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___1791_13673.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___1791_13673.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___1791_13673.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___1791_13673.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___1791_13673.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___1791_13673.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___1791_13673.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___1791_13673.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___1791_13673.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___1791_13673.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___1791_13673.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___1791_13673.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___1791_13673.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___1791_13673.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___1791_13673.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___1791_13673.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___1791_13673.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___1791_13673.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___1791_13673.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___1791_13673.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___1791_13673.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___1791_13673.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___1791_13673.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___1791_13673.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___1791_13673.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___1791_13673.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____13674;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___1791_13673.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___1791_13673.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___1791_13673.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___1791_13673.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___1791_13673.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___1791_13673.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___1791_13673.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___1791_13673.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___1791_13673.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___1791_13673.FStar_TypeChecker_Env.erasable_types_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.SetOptions uu____13675) ->
                  if from_cache
                  then env1
                  else
                    (let uu___1791_13680 = env1  in
                     let uu____13681 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___1791_13680.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___1791_13680.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___1791_13680.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___1791_13680.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___1791_13680.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___1791_13680.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___1791_13680.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___1791_13680.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___1791_13680.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___1791_13680.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___1791_13680.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___1791_13680.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___1791_13680.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___1791_13680.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___1791_13680.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___1791_13680.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___1791_13680.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___1791_13680.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___1791_13680.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___1791_13680.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___1791_13680.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___1791_13680.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___1791_13680.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___1791_13680.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___1791_13680.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___1791_13680.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___1791_13680.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___1791_13680.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___1791_13680.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___1791_13680.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___1791_13680.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___1791_13680.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___1791_13680.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___1791_13680.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____13681;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___1791_13680.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___1791_13680.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___1791_13680.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___1791_13680.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___1791_13680.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___1791_13680.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___1791_13680.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___1791_13680.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___1791_13680.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___1791_13680.FStar_TypeChecker_Env.erasable_types_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.ResetOptions uu____13682) ->
                  if from_cache
                  then env1
                  else
                    (let uu___1791_13689 = env1  in
                     let uu____13690 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___1791_13689.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___1791_13689.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___1791_13689.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___1791_13689.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___1791_13689.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___1791_13689.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___1791_13689.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___1791_13689.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___1791_13689.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___1791_13689.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___1791_13689.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___1791_13689.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___1791_13689.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___1791_13689.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___1791_13689.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___1791_13689.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___1791_13689.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___1791_13689.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___1791_13689.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___1791_13689.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___1791_13689.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___1791_13689.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___1791_13689.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___1791_13689.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___1791_13689.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___1791_13689.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___1791_13689.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___1791_13689.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___1791_13689.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___1791_13689.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___1791_13689.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___1791_13689.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___1791_13689.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___1791_13689.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____13690;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___1791_13689.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___1791_13689.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___1791_13689.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___1791_13689.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___1791_13689.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___1791_13689.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___1791_13689.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___1791_13689.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___1791_13689.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___1791_13689.FStar_TypeChecker_Env.erasable_types_tab)
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
                            let uu____13706 =
                              FStar_Syntax_Util.action_as_lb
                                ne.FStar_Syntax_Syntax.mname a
                                (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Env.push_sigelt env3
                              uu____13706) env2)
              | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
                  FStar_TypeChecker_Env.update_effect_lattice env1 sub1
              | uu____13708 -> env1))
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____13777 se =
        match uu____13777 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____13830 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____13830
              then
                let uu____13833 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____13833
              else ());
             (let uu____13838 = tc_decl env1 se  in
              match uu____13838 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____13891 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____13891
                             then
                               let uu____13895 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____13895
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____13911 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____13911
                             then
                               let uu____13915 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____13915
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
                    (let uu____13933 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____13933
                     then
                       let uu____13938 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____13947 =
                                  let uu____13949 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____13949 "\n"  in
                                Prims.op_Hat s uu____13947) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____13938
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____13959 =
                       let uu____13968 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____13968
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____14010 se1 =
                            match uu____14010 with
                            | (exports1,hidden1) ->
                                let uu____14038 = for_export env3 hidden1 se1
                                   in
                                (match uu____14038 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____13959 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____14192 = acc  in
        match uu____14192 with
        | (uu____14227,uu____14228,env1,uu____14230) ->
            let r =
              let uu____14264 =
                let uu____14268 =
                  let uu____14270 = FStar_TypeChecker_Env.current_module env1
                     in
                  FStar_Ident.string_of_lid uu____14270  in
                FStar_Pervasives_Native.Some uu____14268  in
              FStar_Profiling.profile
                (fun uu____14293  -> process_one_decl acc se) uu____14264
                "FStar.TypeChecker.Tc.process_one_decl"
               in
            ((let uu____14296 = FStar_Options.profile_group_by_decls ()  in
              if uu____14296
              then
                let tag =
                  match FStar_Syntax_Util.lids_of_sigelt se with
                  | hd1::uu____14303 -> FStar_Ident.string_of_lid hd1
                  | uu____14306 ->
                      FStar_Range.string_of_range
                        (FStar_Syntax_Util.range_of_sigelt se)
                   in
                FStar_Profiling.report_and_clear tag
              else ());
             r)
         in
      let uu____14311 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____14311 with
      | (ses1,exports,env1,uu____14359) ->
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
          let uu___1877_14397 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1877_14397.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1877_14397.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1877_14397.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1877_14397.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1877_14397.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1877_14397.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1877_14397.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1877_14397.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1877_14397.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1877_14397.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___1877_14397.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1877_14397.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1877_14397.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1877_14397.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1877_14397.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___1877_14397.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1877_14397.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___1877_14397.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1877_14397.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___1877_14397.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1877_14397.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1877_14397.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1877_14397.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1877_14397.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1877_14397.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1877_14397.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1877_14397.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1877_14397.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1877_14397.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1877_14397.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1877_14397.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1877_14397.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1877_14397.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1877_14397.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___1877_14397.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___1877_14397.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1877_14397.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1877_14397.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1877_14397.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1877_14397.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1877_14397.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1877_14397.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        let check_term lid univs1 t =
          let uu____14417 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____14417 with
          | (univs2,t1) ->
              ((let uu____14425 =
                  let uu____14427 =
                    let uu____14433 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____14433  in
                  FStar_All.pipe_left uu____14427
                    (FStar_Options.Other "Exports")
                   in
                if uu____14425
                then
                  let uu____14437 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____14439 =
                    let uu____14441 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____14441
                      (FStar_String.concat ", ")
                     in
                  let uu____14458 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____14437 uu____14439 uu____14458
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____14464 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____14464 (fun a2  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____14490 =
             let uu____14492 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____14494 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____14492 uu____14494
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____14490);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14505) ->
              let uu____14514 =
                let uu____14516 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14516  in
              if uu____14514
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____14530,uu____14531) ->
              let t =
                let uu____14543 =
                  let uu____14550 =
                    let uu____14551 =
                      let uu____14566 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____14566)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____14551  in
                  FStar_Syntax_Syntax.mk uu____14550  in
                uu____14543 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____14582,uu____14583,uu____14584) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____14594 =
                let uu____14596 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14596  in
              if uu____14594 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____14604,lbs),uu____14606) ->
              let uu____14617 =
                let uu____14619 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14619  in
              if uu____14617
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
              let uu____14642 =
                let uu____14644 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14644  in
              if uu____14642
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____14665 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____14666 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14673 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14674 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____14675 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____14676 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____14683 -> ()  in
        let uu____14684 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____14684 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____14790) -> true
             | uu____14792 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____14822 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____14861 ->
                   let uu____14862 =
                     let uu____14869 =
                       let uu____14870 =
                         let uu____14885 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____14885)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____14870  in
                     FStar_Syntax_Syntax.mk uu____14869  in
                   uu____14862 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____14902,uu____14903) ->
            let s1 =
              let uu___2003_14913 = s  in
              let uu____14914 =
                let uu____14915 =
                  let uu____14922 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____14922)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____14915  in
              let uu____14923 =
                let uu____14926 =
                  let uu____14929 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____14929  in
                FStar_Syntax_Syntax.Assumption :: uu____14926  in
              {
                FStar_Syntax_Syntax.sigel = uu____14914;
                FStar_Syntax_Syntax.sigrng =
                  (uu___2003_14913.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____14923;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2003_14913.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___2003_14913.FStar_Syntax_Syntax.sigattrs);
                FStar_Syntax_Syntax.sigopts =
                  (uu___2003_14913.FStar_Syntax_Syntax.sigopts)
              }  in
            [s1]
        | uu____14932 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____14957 lbdef =
        match uu____14957 with
        | (uvs,t) ->
            let attrs =
              let uu____14968 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____14968
              then
                let uu____14973 =
                  let uu____14974 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____14974
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____14973 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___2016_14977 = s  in
            let uu____14978 =
              let uu____14981 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____14981  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___2016_14977.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____14978;
              FStar_Syntax_Syntax.sigmeta =
                (uu___2016_14977.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs;
              FStar_Syntax_Syntax.sigopts =
                (uu___2016_14977.FStar_Syntax_Syntax.sigopts)
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____14999 -> failwith "Impossible!"  in
        let c_opt =
          let uu____15006 = FStar_Syntax_Util.is_unit t  in
          if uu____15006
          then
            let uu____15013 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____15013
          else
            (let uu____15020 =
               let uu____15021 = FStar_Syntax_Subst.compress t  in
               uu____15021.FStar_Syntax_Syntax.n  in
             match uu____15020 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____15028,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____15052 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____15064 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____15064
            then false
            else
              (let uu____15071 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____15071
               then true
               else
                 (let uu____15078 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____15078))
         in
      let extract_sigelt s =
        (let uu____15090 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____15090
         then
           let uu____15093 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____15093
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____15100 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____15120 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____15139 ->
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
                             (lid,uu____15185,uu____15186,uu____15187,uu____15188,uu____15189)
                             ->
                             ((let uu____15199 =
                                 let uu____15202 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____15202  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____15199);
                              (let uu____15251 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____15251 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____15255,uu____15256,uu____15257,uu____15258,uu____15259)
                             ->
                             ((let uu____15267 =
                                 let uu____15270 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____15270  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____15267);
                              sigelts1)
                         | uu____15319 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____15328 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15328
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____15338 =
                    let uu___2080_15339 = s  in
                    let uu____15340 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2080_15339.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2080_15339.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15340;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2080_15339.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2080_15339.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___2080_15339.FStar_Syntax_Syntax.sigopts)
                    }  in
                  [uu____15338])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____15351 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15351
             then []
             else
               (let uu____15358 = lbs  in
                match uu____15358 with
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
                        (fun uu____15420  ->
                           match uu____15420 with
                           | (uu____15428,t,uu____15430) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____15447  ->
                             match uu____15447 with
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
                           (fun uu____15474  ->
                              match uu____15474 with
                              | (uu____15482,t,uu____15484) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____15496,uu____15497) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____15505 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____15534 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____15534) uu____15505
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____15538 =
                    let uu___2122_15539 = s  in
                    let uu____15540 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2122_15539.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2122_15539.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15540;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2122_15539.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2122_15539.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___2122_15539.FStar_Syntax_Syntax.sigopts)
                    }  in
                  [uu____15538]
                else [])
             else
               (let uu____15547 =
                  let uu___2124_15548 = s  in
                  let uu____15549 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___2124_15548.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___2124_15548.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____15549;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___2124_15548.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___2124_15548.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___2124_15548.FStar_Syntax_Syntax.sigopts)
                  }  in
                [uu____15547])
         | FStar_Syntax_Syntax.Sig_new_effect uu____15552 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15553 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____15554 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15555 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____15568 -> [s])
         in
      let uu___2136_15569 = m  in
      let uu____15570 =
        let uu____15571 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____15571 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___2136_15569.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____15570;
        FStar_Syntax_Syntax.exports =
          (uu___2136_15569.FStar_Syntax_Syntax.exports);
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
        (fun uu____15622  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____15669  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____15684 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____15684
  
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
      (let uu____15773 = FStar_Options.debug_any ()  in
       if uu____15773
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
         let uu___2161_15789 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___2161_15789.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___2161_15789.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___2161_15789.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___2161_15789.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___2161_15789.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___2161_15789.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___2161_15789.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___2161_15789.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___2161_15789.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___2161_15789.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___2161_15789.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___2161_15789.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___2161_15789.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___2161_15789.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___2161_15789.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___2161_15789.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___2161_15789.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___2161_15789.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___2161_15789.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___2161_15789.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___2161_15789.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___2161_15789.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___2161_15789.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___2161_15789.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___2161_15789.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___2161_15789.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___2161_15789.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___2161_15789.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___2161_15789.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___2161_15789.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___2161_15789.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___2161_15789.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___2161_15789.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___2161_15789.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___2161_15789.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___2161_15789.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___2161_15789.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___2161_15789.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___2161_15789.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___2161_15789.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___2161_15789.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___2161_15789.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___2161_15789.FStar_TypeChecker_Env.erasable_types_tab)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____15791 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____15791 with
       | (ses,exports,env3) ->
           ((let uu___2169_15824 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___2169_15824.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___2169_15824.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___2169_15824.FStar_Syntax_Syntax.is_interface)
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
        let uu____15853 = tc_decls env decls  in
        match uu____15853 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___2178_15884 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___2178_15884.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___2178_15884.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___2178_15884.FStar_Syntax_Syntax.is_interface)
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
        let uu____15945 = tc_partial_modul env01 m  in
        match uu____15945 with
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
                (let uu____15982 = FStar_Errors.get_err_count ()  in
                 uu____15982 = Prims.int_zero)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____15993 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____15993
                then
                  let uu____15997 =
                    let uu____15999 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____15999 then "" else " (in lax mode) "  in
                  let uu____16007 =
                    let uu____16009 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16009
                    then
                      let uu____16013 =
                        let uu____16015 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.op_Hat uu____16015 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____16013
                    else ""  in
                  let uu____16022 =
                    let uu____16024 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16024
                    then
                      let uu____16028 =
                        let uu____16030 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____16030 "\n"  in
                      Prims.op_Hat "\nto: " uu____16028
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____15997
                    uu____16007 uu____16022
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___2204_16044 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2204_16044.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2204_16044.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2204_16044.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2204_16044.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2204_16044.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2204_16044.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2204_16044.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2204_16044.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2204_16044.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2204_16044.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2204_16044.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2204_16044.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2204_16044.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2204_16044.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2204_16044.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2204_16044.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2204_16044.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2204_16044.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2204_16044.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2204_16044.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2204_16044.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2204_16044.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2204_16044.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2204_16044.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2204_16044.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2204_16044.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2204_16044.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2204_16044.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2204_16044.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2204_16044.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2204_16044.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___2204_16044.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2204_16044.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2204_16044.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2204_16044.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2204_16044.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2204_16044.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2204_16044.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2204_16044.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2204_16044.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2204_16044.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2204_16044.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2204_16044.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___2204_16044.FStar_TypeChecker_Env.erasable_types_tab)
                    }  in
                  let en02 =
                    let uu___2207_16046 = en01  in
                    let uu____16047 =
                      let uu____16062 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____16062, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2207_16046.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2207_16046.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2207_16046.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2207_16046.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2207_16046.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2207_16046.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2207_16046.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2207_16046.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2207_16046.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2207_16046.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2207_16046.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2207_16046.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2207_16046.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2207_16046.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2207_16046.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2207_16046.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2207_16046.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2207_16046.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2207_16046.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2207_16046.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2207_16046.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2207_16046.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2207_16046.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2207_16046.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2207_16046.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2207_16046.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2207_16046.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2207_16046.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2207_16046.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2207_16046.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2207_16046.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____16047;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2207_16046.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2207_16046.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2207_16046.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2207_16046.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2207_16046.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2207_16046.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2207_16046.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2207_16046.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2207_16046.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___2207_16046.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2207_16046.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2207_16046.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___2207_16046.FStar_TypeChecker_Env.erasable_types_tab)
                    }  in
                  let uu____16108 =
                    let uu____16110 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____16110  in
                  if uu____16108
                  then
                    ((let uu____16114 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____16114 (fun a3  -> ()));
                     en02)
                  else en02  in
                let uu____16118 = tc_modul en0 modul_iface true  in
                match uu____16118 with
                | (modul_iface1,env) ->
                    ((let uu___2216_16131 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___2216_16131.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___2216_16131.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___2216_16131.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___2218_16135 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___2218_16135.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___2218_16135.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___2218_16135.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____16138 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____16138 FStar_Util.smap_clear);
               (let uu____16174 =
                  ((let uu____16178 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____16178) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____16181 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____16181)
                   in
                if uu____16174 then check_exports env modul exports else ());
               (let uu____16187 =
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____16187 (fun a4  -> ()));
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
        let uu____16202 =
          let uu____16204 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____16204  in
        push_context env uu____16202  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = add_sigelt_to_env env2 se true  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____16226 =
                         FStar_TypeChecker_Env.lookup_sigelt env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____16229 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____16229 with | (uu____16236,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____16261 = FStar_Options.debug_any ()  in
         if uu____16261
         then
           let uu____16264 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____16264
         else ());
        (let uu____16276 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____16276
         then
           let uu____16279 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____16279
         else ());
        (let env1 =
           let uu___2248_16285 = env  in
           let uu____16286 =
             let uu____16288 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____16288  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___2248_16285.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___2248_16285.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___2248_16285.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___2248_16285.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___2248_16285.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___2248_16285.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___2248_16285.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___2248_16285.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___2248_16285.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___2248_16285.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___2248_16285.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___2248_16285.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___2248_16285.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___2248_16285.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___2248_16285.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___2248_16285.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___2248_16285.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___2248_16285.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___2248_16285.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___2248_16285.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____16286;
             FStar_TypeChecker_Env.lax_universes =
               (uu___2248_16285.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___2248_16285.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___2248_16285.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___2248_16285.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___2248_16285.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___2248_16285.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___2248_16285.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___2248_16285.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___2248_16285.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___2248_16285.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___2248_16285.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___2248_16285.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___2248_16285.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___2248_16285.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___2248_16285.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___2248_16285.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___2248_16285.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___2248_16285.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___2248_16285.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___2248_16285.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___2248_16285.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___2248_16285.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___2248_16285.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___2248_16285.FStar_TypeChecker_Env.erasable_types_tab)
           }  in
         let uu____16290 = tc_modul env1 m b  in
         match uu____16290 with
         | (m1,env2) ->
             ((let uu____16302 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____16302
               then
                 let uu____16305 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____16305
               else ());
              (let uu____16311 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____16311
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
                         let uu____16349 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____16349 with
                         | (univnames1,e) ->
                             let uu___2270_16356 = lb  in
                             let uu____16357 =
                               let uu____16360 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____16360 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2270_16356.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2270_16356.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___2270_16356.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2270_16356.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16357;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2270_16356.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2270_16356.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___2272_16361 = se  in
                       let uu____16362 =
                         let uu____16363 =
                           let uu____16370 =
                             let uu____16371 = FStar_List.map update lbs  in
                             (b1, uu____16371)  in
                           (uu____16370, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____16363  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____16362;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___2272_16361.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___2272_16361.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___2272_16361.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___2272_16361.FStar_Syntax_Syntax.sigattrs);
                         FStar_Syntax_Syntax.sigopts =
                           (uu___2272_16361.FStar_Syntax_Syntax.sigopts)
                       }
                   | uu____16379 -> se  in
                 let normalized_module =
                   let uu___2276_16381 = m1  in
                   let uu____16382 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___2276_16381.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____16382;
                     FStar_Syntax_Syntax.exports =
                       (uu___2276_16381.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___2276_16381.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____16383 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____16383
               else ());
              (m1, env2)))
  