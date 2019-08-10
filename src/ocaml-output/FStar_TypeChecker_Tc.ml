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
                                                                 (uu___310_2898.FStar_TypeChecker_Env.strict_args_tab)
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
                                                             (uu___340_3042.FStar_TypeChecker_Env.strict_args_tab)
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
               FStar_Syntax_Syntax.sigattrs = uu____6417;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____6419,_t_top,_lex_t_top,_6453,uu____6422);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____6424;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____6425;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____6427,_t_cons,_lex_t_cons,_6461,uu____6430);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____6432;
                 FStar_Syntax_Syntax.sigattrs = uu____6433;_}::[]
               when
               ((_6453 = Prims.int_zero) && (_6461 = Prims.int_zero)) &&
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
                 let uu____6486 =
                   let uu____6493 =
                     let uu____6494 =
                       let uu____6501 =
                         let uu____6504 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____6504
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____6501, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____6494  in
                   FStar_Syntax_Syntax.mk uu____6493  in
                 uu____6486 FStar_Pervasives_Native.None r1  in
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
                   let uu____6519 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6519
                    in
                 let hd1 =
                   let uu____6521 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6521
                    in
                 let tl1 =
                   let uu____6523 =
                     let uu____6524 =
                       let uu____6531 =
                         let uu____6532 =
                           let uu____6539 =
                             let uu____6542 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____6542
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____6539, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____6532  in
                       FStar_Syntax_Syntax.mk uu____6531  in
                     uu____6524 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6523
                    in
                 let res =
                   let uu____6548 =
                     let uu____6555 =
                       let uu____6556 =
                         let uu____6563 =
                           let uu____6566 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____6566
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____6563,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____6556  in
                     FStar_Syntax_Syntax.mk uu____6555  in
                   uu____6548 FStar_Pervasives_Native.None r2  in
                 let uu____6569 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____6569
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
               let uu____6608 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____6608;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____6613 ->
               let err_msg =
                 let uu____6618 =
                   let uu____6620 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____6620  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____6618
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
    fun uu____6645  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____6645 with
          | (uvs,t) ->
              let uu____6658 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____6658 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____6670 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____6670 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____6688 =
                        let uu____6691 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____6691
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____6688)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____6714 =
          let uu____6715 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____6715 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____6714 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____6740 =
          let uu____6741 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____6741 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____6740 r
  
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
          (let uu____6790 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____6790
           then
             let uu____6793 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____6793
           else ());
          (let uu____6798 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____6798 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____6829 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____6829 FStar_List.flatten  in
               ((let uu____6843 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____6846 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____6846)
                    in
                 if uu____6843
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
                           let uu____6862 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____6872,uu____6873,uu____6874,uu____6875,uu____6876)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____6885 -> failwith "Impossible!"  in
                           match uu____6862 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Inductive type "
                                      (Prims.op_Hat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____6904 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____6914,uu____6915,ty_lid,uu____6917,uu____6918)
                               -> (data_lid, ty_lid)
                           | uu____6925 -> failwith "Impossible"  in
                         match uu____6904 with
                         | (data_lid,ty_lid) ->
                             let uu____6933 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____6936 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____6936)
                                in
                             if uu____6933
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Exception "
                                      (Prims.op_Hat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____6950 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____6955,uu____6956,uu____6957,uu____6958,uu____6959)
                         -> lid
                     | uu____6968 -> failwith "Impossible"  in
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
                   let uu____6986 =
                     (((FStar_List.length tcs) = Prims.int_zero) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____6986
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
          let pop1 uu____7061 =
            let uu____7062 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___879_7072  ->
               match () with
               | () ->
                   let uu____7079 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____7079 (fun r  -> pop1 (); r)) ()
          with | uu___878_7110 -> (pop1 (); FStar_Exn.raise uu___878_7110)
  
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
      | uu____7426 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____7484 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____7484 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____7509 .
    'Auu____7509 FStar_Pervasives_Native.option -> 'Auu____7509 Prims.list
  =
  fun uu___0_7518  ->
    match uu___0_7518 with
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
            let uu____7598 = collect1 tl1  in
            (match uu____7598 with
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
        | ((e,n1)::uu____7836,[]) ->
            FStar_Pervasives_Native.Some (e, n1, Prims.int_zero)
        | ([],(e,n1)::uu____7892) ->
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
          let uu____8102 =
            let uu____8104 = FStar_Options.ide ()  in
            Prims.op_Negation uu____8104  in
          if uu____8102
          then
            let uu____8107 =
              let uu____8112 = FStar_TypeChecker_Env.dsenv env  in
              let uu____8113 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____8112 uu____8113  in
            (match uu____8107 with
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
                              let uu____8146 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____8147 =
                                let uu____8153 =
                                  let uu____8155 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____8157 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____8155 uu____8157
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____8153)
                                 in
                              FStar_Errors.log_issue uu____8146 uu____8147
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____8164 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____8165 =
                                   let uu____8171 =
                                     let uu____8173 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____8173
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____8171)
                                    in
                                 FStar_Errors.log_issue uu____8164 uu____8165)
                              else ())
                         else ())))
          else ()
      | uu____8183 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____8228 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____8256 ->
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
             let uu____8316 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____8316
             then
               let ses1 =
                 let uu____8324 =
                   let uu____8325 =
                     let uu____8326 =
                       tc_inductive
                         (let uu___1011_8335 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1011_8335.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1011_8335.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1011_8335.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1011_8335.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1011_8335.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1011_8335.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1011_8335.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1011_8335.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1011_8335.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1011_8335.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1011_8335.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1011_8335.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1011_8335.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1011_8335.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1011_8335.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1011_8335.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1011_8335.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1011_8335.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1011_8335.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1011_8335.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1011_8335.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___1011_8335.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1011_8335.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1011_8335.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1011_8335.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1011_8335.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1011_8335.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1011_8335.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1011_8335.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1011_8335.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1011_8335.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1011_8335.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1011_8335.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1011_8335.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1011_8335.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1011_8335.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1011_8335.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1011_8335.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1011_8335.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1011_8335.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1011_8335.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1011_8335.FStar_TypeChecker_Env.strict_args_tab)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____8326
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____8325
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____8324
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____8349 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____8349
                 then
                   let uu____8354 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1015_8358 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1015_8358.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1015_8358.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1015_8358.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1015_8358.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____8354
                 else ());
                ses1)
             else ses  in
           let uu____8368 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____8368 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___1022_8392 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1022_8392.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1022_8392.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1022_8392.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1022_8392.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____8404 = cps_and_elaborate env ne  in
           (match uu____8404 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___1036_8443 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1036_8443.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1036_8443.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1036_8443.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1036_8443.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___1039_8445 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1039_8445.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1039_8445.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1039_8445.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1039_8445.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses), env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 =
             let uu____8452 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env)
                in
             if uu____8452
             then
               let ne1 =
                 let uu____8456 =
                   let uu____8457 =
                     let uu____8458 =
                       tc_eff_decl
                         (let uu___1045_8461 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1045_8461.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1045_8461.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1045_8461.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1045_8461.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1045_8461.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1045_8461.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1045_8461.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1045_8461.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1045_8461.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1045_8461.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1045_8461.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1045_8461.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1045_8461.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1045_8461.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1045_8461.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1045_8461.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1045_8461.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1045_8461.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1045_8461.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1045_8461.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1045_8461.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___1045_8461.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1045_8461.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1045_8461.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1045_8461.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1045_8461.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1045_8461.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1045_8461.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1045_8461.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1045_8461.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1045_8461.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1045_8461.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1045_8461.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1045_8461.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1045_8461.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1045_8461.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1045_8461.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1045_8461.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1045_8461.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1045_8461.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1045_8461.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1045_8461.FStar_TypeChecker_Env.strict_args_tab)
                          }) ne
                        in
                     FStar_All.pipe_right uu____8458
                       (fun ne1  ->
                          let uu___1048_8467 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1048_8467.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1048_8467.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1048_8467.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1048_8467.FStar_Syntax_Syntax.sigattrs)
                          })
                      in
                   FStar_All.pipe_right uu____8457
                     (FStar_TypeChecker_Normalize.elim_uvars env)
                    in
                 FStar_All.pipe_right uu____8456
                   FStar_Syntax_Util.eff_decl_of_new_effect
                  in
               ((let uu____8469 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____8469
                 then
                   let uu____8474 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1052_8478 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1052_8478.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1052_8478.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1052_8478.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1052_8478.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Effect decl after phase 1: %s\n"
                     uu____8474
                 else ());
                ne1)
             else ne  in
           let ne2 = tc_eff_decl env ne1  in
           let se1 =
             let uu___1057_8486 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne2);
               FStar_Syntax_Syntax.sigrng =
                 (uu___1057_8486.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___1057_8486.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___1057_8486.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___1057_8486.FStar_Syntax_Syntax.sigattrs)
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
           let uu____8494 =
             let uu____8501 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____8501
              in
           (match uu____8494 with
            | (a,wp_a_src) ->
                let uu____8518 =
                  let uu____8525 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____8525
                   in
                (match uu____8518 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____8543 =
                         let uu____8546 =
                           let uu____8547 =
                             let uu____8554 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____8554)  in
                           FStar_Syntax_Syntax.NT uu____8547  in
                         [uu____8546]  in
                       FStar_Syntax_Subst.subst uu____8543 wp_b_tgt  in
                     let expected_k =
                       let uu____8562 =
                         let uu____8571 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____8578 =
                           let uu____8587 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____8587]  in
                         uu____8571 :: uu____8578  in
                       let uu____8612 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____8562 uu____8612  in
                     let repr_type eff_name a1 wp =
                       (let uu____8634 =
                          let uu____8636 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name
                             in
                          Prims.op_Negation uu____8636  in
                        if uu____8634
                        then
                          let uu____8639 =
                            let uu____8645 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____8645)
                             in
                          let uu____8649 =
                            FStar_TypeChecker_Env.get_range env  in
                          FStar_Errors.raise_error uu____8639 uu____8649
                        else ());
                       (let uu____8652 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name
                           in
                        match uu____8652 with
                        | FStar_Pervasives_Native.None  ->
                            failwith
                              "internal error: reifiable effect has no decl?"
                        | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                            let repr =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [FStar_Syntax_Syntax.U_unknown] env ed
                                ed.FStar_Syntax_Syntax.repr
                               in
                            let uu____8685 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____8686 =
                              let uu____8693 =
                                let uu____8694 =
                                  let uu____8711 =
                                    let uu____8722 =
                                      FStar_Syntax_Syntax.as_arg a1  in
                                    let uu____8731 =
                                      let uu____8742 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8742]  in
                                    uu____8722 :: uu____8731  in
                                  (repr, uu____8711)  in
                                FStar_Syntax_Syntax.Tm_app uu____8694  in
                              FStar_Syntax_Syntax.mk uu____8693  in
                            uu____8686 FStar_Pervasives_Native.None
                              uu____8685)
                        in
                     let uu____8787 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____8960 =
                             if (FStar_List.length uvs) > Prims.int_zero
                             then
                               let uu____8971 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____8971 with
                               | (usubst,uvs1) ->
                                   let uu____8994 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____8995 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____8994, uu____8995)
                             else (env, lift_wp)  in
                           (match uu____8960 with
                            | (env1,lift_wp1) ->
                                let lift_wp2 =
                                  if (FStar_List.length uvs) = Prims.int_zero
                                  then check_and_gen env1 lift_wp1 expected_k
                                  else
                                    (let lift_wp2 =
                                       tc_check_trivial_guard env1 lift_wp1
                                         expected_k
                                        in
                                     let uu____9045 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____9045))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____9116 =
                             if (FStar_List.length what) > Prims.int_zero
                             then
                               let uu____9131 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____9131 with
                               | (usubst,uvs) ->
                                   let uu____9156 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____9156)
                             else ([], lift)  in
                           (match uu____9116 with
                            | (uvs,lift1) ->
                                ((let uu____9192 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____9192
                                  then
                                    let uu____9196 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____9196
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____9202 =
                                    let uu____9209 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____9209 lift1
                                     in
                                  match uu____9202 with
                                  | (lift2,comp,uu____9234) ->
                                      let uu____9235 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____9235 with
                                       | (uu____9264,lift_wp,lift_elab) ->
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
                                             let uu____9296 =
                                               let uu____9307 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____9307
                                                in
                                             let uu____9324 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____9296, uu____9324)
                                           else
                                             (let uu____9353 =
                                                let uu____9364 =
                                                  let uu____9373 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____9373)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____9364
                                                 in
                                              let uu____9388 =
                                                let uu____9397 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____9397)  in
                                              (uu____9353, uu____9388))))))
                        in
                     (match uu____8787 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___1133_9471 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1133_9471.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1133_9471.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1133_9471.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1133_9471.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1133_9471.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1133_9471.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1133_9471.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1133_9471.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1133_9471.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1133_9471.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1133_9471.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1133_9471.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1133_9471.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1133_9471.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1133_9471.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1133_9471.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1133_9471.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1133_9471.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1133_9471.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1133_9471.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1133_9471.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1133_9471.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1133_9471.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1133_9471.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1133_9471.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1133_9471.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1133_9471.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1133_9471.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1133_9471.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1133_9471.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1133_9471.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1133_9471.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1133_9471.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1133_9471.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1133_9471.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1133_9471.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1133_9471.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1133_9471.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1133_9471.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1133_9471.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1133_9471.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1133_9471.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1133_9471.FStar_TypeChecker_Env.strict_args_tab)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____9528 =
                                  let uu____9533 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____9533 with
                                  | (usubst,uvs1) ->
                                      let uu____9556 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____9557 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____9556, uu____9557)
                                   in
                                (match uu____9528 with
                                 | (env2,lift2) ->
                                     let uu____9570 =
                                       let uu____9577 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____9577
                                        in
                                     (match uu____9570 with
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
                                              let uu____9611 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____9612 =
                                                let uu____9619 =
                                                  let uu____9620 =
                                                    let uu____9637 =
                                                      let uu____9648 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____9657 =
                                                        let uu____9668 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____9668]  in
                                                      uu____9648 ::
                                                        uu____9657
                                                       in
                                                    (lift_wp1, uu____9637)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____9620
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____9619
                                                 in
                                              uu____9612
                                                FStar_Pervasives_Native.None
                                                uu____9611
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____9716 =
                                              let uu____9725 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____9732 =
                                                let uu____9741 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____9748 =
                                                  let uu____9757 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____9757]  in
                                                uu____9741 :: uu____9748  in
                                              uu____9725 :: uu____9732  in
                                            let uu____9788 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____9716 uu____9788
                                             in
                                          let uu____9791 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____9791 with
                                           | (expected_k2,uu____9809,uu____9810)
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
                                                    let uu____9834 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____9834))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____9850 =
                              let uu____9852 =
                                let uu____9854 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____9854
                                  FStar_List.length
                                 in
                              uu____9852 <> Prims.int_one  in
                            if uu____9850
                            then
                              let uu____9876 =
                                let uu____9882 =
                                  let uu____9884 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____9886 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____9888 =
                                    let uu____9890 =
                                      let uu____9892 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____9892
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____9890
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____9884 uu____9886 uu____9888
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____9882)
                                 in
                              FStar_Errors.raise_error uu____9876 r
                            else ());
                           (let uu____9919 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____9930 =
                                   let uu____9932 =
                                     let uu____9935 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____9935
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____9932
                                     FStar_List.length
                                    in
                                 uu____9930 <> Prims.int_one)
                               in
                            if uu____9919
                            then
                              let uu____9989 =
                                let uu____9995 =
                                  let uu____9997 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____9999 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10001 =
                                    let uu____10003 =
                                      let uu____10005 =
                                        let uu____10008 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____10008
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10005
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10003
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____9997 uu____9999 uu____10001
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____9995)
                                 in
                              FStar_Errors.raise_error uu____9989 r
                            else ());
                           (let sub2 =
                              let uu___1170_10067 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___1170_10067.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___1170_10067.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___1173_10069 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___1173_10069.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___1173_10069.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___1173_10069.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___1173_10069.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let uu____10083 =
             if (FStar_List.length uvs) = Prims.int_zero
             then (env, uvs, tps, c)
             else
               (let uu____10111 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____10111 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____10142 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____10142 c  in
                    let uu____10151 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____10151, uvs1, tps1, c1))
              in
           (match uu____10083 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____10173 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____10173 with
                 | (tps2,c2) ->
                     let uu____10190 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____10190 with
                      | (tps3,env3,us) ->
                          let uu____10210 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____10210 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____10238)::uu____10239 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____10258 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____10266 =
                                   let uu____10268 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____10268  in
                                 if uu____10266
                                 then
                                   let uu____10271 =
                                     let uu____10277 =
                                       let uu____10279 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____10281 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____10279 uu____10281
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____10277)
                                      in
                                   FStar_Errors.raise_error uu____10271 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____10289 =
                                   let uu____10290 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____10290
                                    in
                                 match uu____10289 with
                                 | (uvs2,t) ->
                                     let uu____10321 =
                                       let uu____10326 =
                                         let uu____10339 =
                                           let uu____10340 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____10340.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____10339)  in
                                       match uu____10326 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____10355,c5)) -> ([], c5)
                                       | (uu____10397,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____10436 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____10321 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               Prims.int_one
                                           then
                                             (let uu____10470 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____10470 with
                                              | (uu____10475,t1) ->
                                                  let uu____10477 =
                                                    let uu____10483 =
                                                      let uu____10485 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____10487 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____10491 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____10485
                                                        uu____10487
                                                        uu____10491
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____10483)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____10477 r)
                                           else ();
                                           (let se1 =
                                              let uu___1243_10498 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___1243_10498.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___1243_10498.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___1243_10498.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___1243_10498.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____10505,uu____10506,uu____10507) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_10512  ->
                   match uu___1_10512 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____10515 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____10521,uu____10522) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_10531  ->
                   match uu___1_10531 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____10534 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____10545 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____10545
             then
               let uu____10548 =
                 let uu____10554 =
                   let uu____10556 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____10556
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____10554)
                  in
               FStar_Errors.raise_error uu____10548 r
             else ());
            (let uu____10562 =
               let uu____10571 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____10571
               then
                 let uu____10582 =
                   tc_declare_typ
                     (let uu___1267_10585 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1267_10585.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1267_10585.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1267_10585.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1267_10585.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1267_10585.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1267_10585.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1267_10585.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1267_10585.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1267_10585.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1267_10585.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1267_10585.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1267_10585.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1267_10585.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1267_10585.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1267_10585.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1267_10585.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1267_10585.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1267_10585.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1267_10585.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1267_10585.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1267_10585.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1267_10585.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1267_10585.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1267_10585.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1267_10585.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1267_10585.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1267_10585.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1267_10585.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1267_10585.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1267_10585.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1267_10585.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1267_10585.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1267_10585.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1267_10585.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1267_10585.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1267_10585.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1267_10585.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1267_10585.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1267_10585.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1267_10585.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___1267_10585.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___1267_10585.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1267_10585.FStar_TypeChecker_Env.strict_args_tab)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____10582 with
                 | (uvs1,t1) ->
                     ((let uu____10610 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____10610
                       then
                         let uu____10615 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____10617 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____10615 uu____10617
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____10562 with
             | (uvs1,t1) ->
                 let uu____10652 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____10652 with
                  | (uvs2,t2) ->
                      ([(let uu___1280_10682 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1280_10682.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1280_10682.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1280_10682.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1280_10682.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____10687 =
             let uu____10696 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____10696
             then
               let uu____10707 =
                 tc_assume
                   (let uu___1289_10710 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1289_10710.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1289_10710.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1289_10710.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1289_10710.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1289_10710.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1289_10710.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1289_10710.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1289_10710.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1289_10710.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1289_10710.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1289_10710.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1289_10710.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1289_10710.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1289_10710.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1289_10710.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1289_10710.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1289_10710.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1289_10710.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1289_10710.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1289_10710.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1289_10710.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___1289_10710.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1289_10710.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1289_10710.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1289_10710.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1289_10710.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1289_10710.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1289_10710.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1289_10710.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1289_10710.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1289_10710.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1289_10710.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1289_10710.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1289_10710.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1289_10710.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1289_10710.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1289_10710.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1289_10710.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1289_10710.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1289_10710.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1289_10710.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1289_10710.FStar_TypeChecker_Env.strict_args_tab)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____10707 with
               | (uvs1,t1) ->
                   ((let uu____10736 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____10736
                     then
                       let uu____10741 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10743 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____10741
                         uu____10743
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____10687 with
            | (uvs1,t1) ->
                let uu____10778 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____10778 with
                 | (uvs2,t2) ->
                     ([(let uu___1302_10808 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1302_10808.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1302_10808.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1302_10808.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1302_10808.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____10812 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____10812 with
            | (e1,c,g1) ->
                let uu____10832 =
                  let uu____10839 =
                    let uu____10842 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____10842  in
                  let uu____10843 =
                    let uu____10848 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____10848)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____10839 uu____10843
                   in
                (match uu____10832 with
                 | (e2,uu____10860,g) ->
                     ((let uu____10863 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____10863);
                      (let se1 =
                         let uu___1317_10865 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1317_10865.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1317_10865.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1317_10865.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1317_10865.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____10877 = FStar_Options.debug_any ()  in
             if uu____10877
             then
               let uu____10880 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____10882 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____10880
                 uu____10882
             else ());
            (let uu____10887 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____10887 with
             | (t1,uu____10905,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____10919 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____10919 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____10922 =
                              let uu____10928 =
                                let uu____10930 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____10932 =
                                  let uu____10934 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____10934
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____10930 uu____10932
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____10928)
                               in
                            FStar_Errors.raise_error uu____10922 r
                        | uu____10946 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___1338_10951 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1338_10951.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1338_10951.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1338_10951.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1338_10951.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1338_10951.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1338_10951.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1338_10951.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1338_10951.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1338_10951.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1338_10951.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1338_10951.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1338_10951.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1338_10951.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1338_10951.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1338_10951.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1338_10951.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1338_10951.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1338_10951.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1338_10951.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1338_10951.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___1338_10951.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1338_10951.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1338_10951.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1338_10951.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1338_10951.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1338_10951.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1338_10951.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1338_10951.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1338_10951.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1338_10951.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1338_10951.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1338_10951.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1338_10951.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1338_10951.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1338_10951.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1338_10951.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1338_10951.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1338_10951.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1338_10951.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1338_10951.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1338_10951.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___1338_10951.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1338_10951.FStar_TypeChecker_Env.strict_args_tab)
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
                 let uu____11019 =
                   let uu____11021 =
                     let uu____11030 = drop_logic val_q  in
                     let uu____11033 = drop_logic q'  in
                     (uu____11030, uu____11033)  in
                   match uu____11021 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____11019
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____11060 =
                      let uu____11066 =
                        let uu____11068 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____11070 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____11072 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____11068 uu____11070 uu____11072
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____11066)
                       in
                    FStar_Errors.raise_error uu____11060 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____11109 =
                   let uu____11110 = FStar_Syntax_Subst.compress def  in
                   uu____11110.FStar_Syntax_Syntax.n  in
                 match uu____11109 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____11122,uu____11123) -> binders
                 | uu____11148 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____11160;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____11265) -> val_bs1
                     | (uu____11296,[]) -> val_bs1
                     | ((body_bv,uu____11328)::bt,(val_bv,aqual)::vt) ->
                         let uu____11385 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____11409) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___1407_11423 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___1409_11426 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___1409_11426.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___1407_11423.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1407_11423.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____11385
                      in
                   let uu____11433 =
                     let uu____11440 =
                       let uu____11441 =
                         let uu____11456 = rename_binders1 def_bs val_bs  in
                         (uu____11456, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____11441  in
                     FStar_Syntax_Syntax.mk uu____11440  in
                   uu____11433 FStar_Pervasives_Native.None r1
               | uu____11475 -> typ1  in
             let uu___1415_11476 = lb  in
             let uu____11477 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___1415_11476.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1415_11476.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____11477;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1415_11476.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___1415_11476.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1415_11476.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1415_11476.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____11480 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____11535  ->
                     fun lb  ->
                       match uu____11535 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____11581 =
                             let uu____11593 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____11593 with
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
                                   | uu____11673 ->
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
                                  (let uu____11720 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____11720, quals_opt1)))
                              in
                           (match uu____11581 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____11480 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____11824 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___2_11830  ->
                                match uu___2_11830 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____11835 -> false))
                         in
                      if uu____11824
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____11848 =
                    let uu____11855 =
                      let uu____11856 =
                        let uu____11870 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____11870)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____11856  in
                    FStar_Syntax_Syntax.mk uu____11855  in
                  uu____11848 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___1458_11889 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1458_11889.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1458_11889.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1458_11889.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1458_11889.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1458_11889.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1458_11889.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1458_11889.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1458_11889.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1458_11889.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1458_11889.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1458_11889.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1458_11889.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1458_11889.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1458_11889.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1458_11889.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1458_11889.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1458_11889.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1458_11889.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1458_11889.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1458_11889.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1458_11889.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1458_11889.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1458_11889.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1458_11889.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1458_11889.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1458_11889.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1458_11889.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1458_11889.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1458_11889.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1458_11889.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1458_11889.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1458_11889.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1458_11889.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1458_11889.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1458_11889.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1458_11889.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1458_11889.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1458_11889.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1458_11889.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1458_11889.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1458_11889.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___1458_11889.FStar_TypeChecker_Env.strict_args_tab)
                  }  in
                let e1 =
                  let uu____11892 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____11892
                  then
                    let drop_lbtyp e_lax =
                      let uu____11901 =
                        let uu____11902 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____11902.FStar_Syntax_Syntax.n  in
                      match uu____11901 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____11924 =
                              let uu____11925 = FStar_Syntax_Subst.compress e
                                 in
                              uu____11925.FStar_Syntax_Syntax.n  in
                            match uu____11924 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____11929,lb1::[]),uu____11931) ->
                                let uu____11947 =
                                  let uu____11948 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____11948.FStar_Syntax_Syntax.n  in
                                (match uu____11947 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____11953 -> false)
                            | uu____11955 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___1483_11959 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___1485_11974 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___1485_11974.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___1485_11974.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___1485_11974.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___1485_11974.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___1485_11974.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___1485_11974.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___1483_11959.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___1483_11959.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____11977 -> e_lax  in
                    let uu____11978 =
                      FStar_Util.record_time
                        (fun uu____11986  ->
                           let uu____11987 =
                             let uu____11988 =
                               let uu____11989 =
                                 FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                   (let uu___1489_11998 = env'  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___1489_11998.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___1489_11998.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___1489_11998.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___1489_11998.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___1489_11998.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___1489_11998.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___1489_11998.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___1489_11998.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___1489_11998.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___1489_11998.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___1489_11998.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___1489_11998.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___1489_11998.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___1489_11998.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___1489_11998.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___1489_11998.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___1489_11998.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___1489_11998.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___1489_11998.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___1489_11998.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___1489_11998.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___1489_11998.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___1489_11998.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___1489_11998.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___1489_11998.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___1489_11998.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___1489_11998.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___1489_11998.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___1489_11998.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___1489_11998.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___1489_11998.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___1489_11998.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___1489_11998.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___1489_11998.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___1489_11998.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___1489_11998.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___1489_11998.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___1489_11998.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___1489_11998.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___1489_11998.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___1489_11998.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___1489_11998.FStar_TypeChecker_Env.strict_args_tab)
                                    }) e
                                  in
                               FStar_All.pipe_right uu____11989
                                 (fun uu____12011  ->
                                    match uu____12011 with
                                    | (e1,uu____12019,uu____12020) -> e1)
                                in
                             FStar_All.pipe_right uu____11988
                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                  env')
                              in
                           FStar_All.pipe_right uu____11987 drop_lbtyp)
                       in
                    match uu____11978 with
                    | (e1,ms) ->
                        ((let uu____12026 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TwoPhases")
                             in
                          if uu____12026
                          then
                            let uu____12031 =
                              FStar_Syntax_Print.term_to_string e1  in
                            FStar_Util.print1
                              "Let binding after phase 1: %s\n" uu____12031
                          else ());
                         (let uu____12037 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TCDeclTime")
                             in
                          if uu____12037
                          then
                            let uu____12042 = FStar_Util.string_of_int ms  in
                            FStar_Util.print1
                              "Let binding elaborated (phase 1) in %s milliseconds\n"
                              uu____12042
                          else ());
                         e1)
                  else e  in
                let uu____12049 =
                  let uu____12058 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____12058 with
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
                (match uu____12049 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___1519_12163 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___1519_12163.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1519_12163.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1519_12163.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1519_12163.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___1526_12176 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1526_12176.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1526_12176.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___1526_12176.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___1526_12176.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1526_12176.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1526_12176.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____12177 =
                       FStar_Util.record_time
                         (fun uu____12196  ->
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              env' e1)
                        in
                     (match uu____12177 with
                      | (r1,ms) ->
                          ((let uu____12224 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TCDeclTime")
                               in
                            if uu____12224
                            then
                              let uu____12229 = FStar_Util.string_of_int ms
                                 in
                              FStar_Util.print1
                                "Let binding typechecked in phase 2 in %s milliseconds\n"
                                uu____12229
                            else ());
                           (let uu____12234 =
                              match r1 with
                              | ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                                   FStar_Syntax_Syntax.pos = uu____12259;
                                   FStar_Syntax_Syntax.vars = uu____12260;_},uu____12261,g)
                                  when FStar_TypeChecker_Env.is_trivial g ->
                                  let lbs2 =
                                    let uu____12291 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.snd lbs1)
                                        (FStar_List.map rename_parameters)
                                       in
                                    ((FStar_Pervasives_Native.fst lbs1),
                                      uu____12291)
                                     in
                                  let lbs3 =
                                    let uu____12315 =
                                      match post_tau with
                                      | FStar_Pervasives_Native.Some tau ->
                                          FStar_List.map (postprocess_lb tau)
                                            (FStar_Pervasives_Native.snd lbs2)
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.snd lbs2
                                       in
                                    ((FStar_Pervasives_Native.fst lbs2),
                                      uu____12315)
                                     in
                                  let quals1 =
                                    match e2.FStar_Syntax_Syntax.n with
                                    | FStar_Syntax_Syntax.Tm_meta
                                        (uu____12338,FStar_Syntax_Syntax.Meta_desugared
                                         (FStar_Syntax_Syntax.Masked_effect
                                         ))
                                        ->
                                        FStar_Syntax_Syntax.HasMaskedEffect
                                        :: quals
                                    | uu____12343 -> quals  in
                                  ((let uu___1556_12352 = se1  in
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_let
                                           (lbs3, lids));
                                      FStar_Syntax_Syntax.sigrng =
                                        (uu___1556_12352.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals = quals1;
                                      FStar_Syntax_Syntax.sigmeta =
                                        (uu___1556_12352.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (uu___1556_12352.FStar_Syntax_Syntax.sigattrs)
                                    }), lbs3)
                              | uu____12355 ->
                                  failwith
                                    "impossible (typechecking should preserve Tm_let)"
                               in
                            match uu____12234 with
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
                                 (let uu____12411 = log env1  in
                                  if uu____12411
                                  then
                                    let uu____12414 =
                                      let uu____12416 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.snd lbs1)
                                          (FStar_List.map
                                             (fun lb  ->
                                                let should_log =
                                                  let uu____12436 =
                                                    let uu____12445 =
                                                      let uu____12446 =
                                                        let uu____12449 =
                                                          FStar_Util.right
                                                            lb.FStar_Syntax_Syntax.lbname
                                                           in
                                                        uu____12449.FStar_Syntax_Syntax.fv_name
                                                         in
                                                      uu____12446.FStar_Syntax_Syntax.v
                                                       in
                                                    FStar_TypeChecker_Env.try_lookup_val_decl
                                                      env1 uu____12445
                                                     in
                                                  match uu____12436 with
                                                  | FStar_Pervasives_Native.None
                                                       -> true
                                                  | uu____12458 -> false  in
                                                if should_log
                                                then
                                                  let uu____12470 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  let uu____12472 =
                                                    FStar_Syntax_Print.term_to_string
                                                      lb.FStar_Syntax_Syntax.lbtyp
                                                     in
                                                  FStar_Util.format2
                                                    "let %s : %s" uu____12470
                                                    uu____12472
                                                else ""))
                                         in
                                      FStar_All.pipe_right uu____12416
                                        (FStar_String.concat "\n")
                                       in
                                    FStar_Util.print1 "%s\n" uu____12414
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
      (let uu____12524 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____12524
       then
         let uu____12527 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____12527
       else ());
      (let uu____12532 = get_fail_se se  in
       match uu____12532 with
       | FStar_Pervasives_Native.Some (uu____12553,false ) when
           let uu____12570 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____12570 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___1587_12596 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___1587_12596.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___1587_12596.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___1587_12596.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___1587_12596.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___1587_12596.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___1587_12596.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___1587_12596.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___1587_12596.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___1587_12596.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___1587_12596.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___1587_12596.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___1587_12596.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___1587_12596.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___1587_12596.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___1587_12596.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___1587_12596.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___1587_12596.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___1587_12596.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___1587_12596.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___1587_12596.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___1587_12596.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___1587_12596.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___1587_12596.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___1587_12596.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___1587_12596.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___1587_12596.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___1587_12596.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___1587_12596.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___1587_12596.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___1587_12596.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___1587_12596.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___1587_12596.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___1587_12596.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___1587_12596.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___1587_12596.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___1587_12596.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___1587_12596.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___1587_12596.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___1587_12596.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___1587_12596.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___1587_12596.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___1587_12596.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___1587_12596.FStar_TypeChecker_Env.strict_args_tab)
               }
             else env1  in
           ((let uu____12601 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____12601
             then
               let uu____12604 =
                 let uu____12606 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____12606
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____12604
             else ());
            (let uu____12620 =
               FStar_Errors.catch_errors
                 (fun uu____12650  ->
                    FStar_Options.with_saved_options
                      (fun uu____12662  -> tc_decl' env' se))
                in
             match uu____12620 with
             | (errs,uu____12674) ->
                 ((let uu____12704 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____12704
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____12739 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____12739  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____12751 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____12762 =
                            let uu____12772 = check_multi_eq errnos1 actual
                               in
                            match uu____12772 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- Prims.int_one), (~- Prims.int_one),
                                  (~- Prims.int_one))
                             in
                          (match uu____12762 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____12837 =
                                   let uu____12843 =
                                     let uu____12845 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____12848 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____12851 =
                                       FStar_Util.string_of_int e  in
                                     let uu____12853 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____12855 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____12845 uu____12848 uu____12851
                                       uu____12853 uu____12855
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____12843)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____12837)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____12882 .
    'Auu____12882 ->
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
               (fun uu___3_12925  ->
                  match uu___3_12925 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____12928 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____12939) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____12947 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____12957 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____12962 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____12978 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____13004 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13030) ->
            let uu____13039 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13039
            then
              let for_export_bundle se1 uu____13076 =
                match uu____13076 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____13115,uu____13116) ->
                         let dec =
                           let uu___1663_13126 = se1  in
                           let uu____13127 =
                             let uu____13128 =
                               let uu____13135 =
                                 let uu____13136 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____13136  in
                               (l, us, uu____13135)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____13128
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____13127;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1663_13126.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1663_13126.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1663_13126.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____13146,uu____13147,uu____13148) ->
                         let dec =
                           let uu___1674_13156 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1674_13156.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1674_13156.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1674_13156.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____13161 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____13184,uu____13185,uu____13186) ->
            let uu____13187 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13187 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____13211 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____13211
            then
              ([(let uu___1690_13230 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___1690_13230.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___1690_13230.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___1690_13230.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____13233 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_13239  ->
                         match uu___4_13239 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____13242 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____13248 ->
                             true
                         | uu____13250 -> false))
                  in
               if uu____13233 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____13271 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____13276 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13281 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____13286 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13291 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13309) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____13323 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____13323
            then ([], hidden)
            else
              (let dec =
                 let uu____13344 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____13344;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____13355 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13355
            then
              let uu____13366 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1727_13380 = se  in
                        let uu____13381 =
                          let uu____13382 =
                            let uu____13389 =
                              let uu____13390 =
                                let uu____13393 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____13393.FStar_Syntax_Syntax.fv_name  in
                              uu____13390.FStar_Syntax_Syntax.v  in
                            (uu____13389, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____13382  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____13381;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1727_13380.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1727_13380.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1727_13380.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____13366, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____13416 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____13416
       then
         let uu____13419 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____13419
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____13424 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____13442 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
           uu____13459) ->
           let env1 =
             let uu___1748_13464 = env  in
             let uu____13465 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1748_13464.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1748_13464.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1748_13464.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1748_13464.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1748_13464.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1748_13464.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1748_13464.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1748_13464.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1748_13464.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1748_13464.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1748_13464.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1748_13464.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1748_13464.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1748_13464.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1748_13464.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1748_13464.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1748_13464.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1748_13464.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1748_13464.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1748_13464.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1748_13464.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1748_13464.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1748_13464.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1748_13464.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1748_13464.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1748_13464.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1748_13464.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1748_13464.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1748_13464.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1748_13464.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1748_13464.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1748_13464.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1748_13464.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1748_13464.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____13465;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1748_13464.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1748_13464.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1748_13464.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1748_13464.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1748_13464.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1748_13464.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1748_13464.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1748_13464.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1748_13464.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
           let env1 =
             let uu___1748_13467 = env  in
             let uu____13468 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1748_13467.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1748_13467.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1748_13467.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1748_13467.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1748_13467.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1748_13467.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1748_13467.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1748_13467.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1748_13467.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1748_13467.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1748_13467.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1748_13467.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1748_13467.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1748_13467.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1748_13467.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1748_13467.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1748_13467.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1748_13467.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1748_13467.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1748_13467.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1748_13467.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1748_13467.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1748_13467.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1748_13467.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1748_13467.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1748_13467.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1748_13467.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1748_13467.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1748_13467.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1748_13467.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1748_13467.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1748_13467.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1748_13467.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1748_13467.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____13468;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1748_13467.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1748_13467.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1748_13467.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1748_13467.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1748_13467.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1748_13467.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1748_13467.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1748_13467.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1748_13467.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions
           uu____13469) ->
           let env1 =
             let uu___1748_13472 = env  in
             let uu____13473 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1748_13472.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1748_13472.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1748_13472.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1748_13472.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1748_13472.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1748_13472.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1748_13472.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1748_13472.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1748_13472.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1748_13472.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1748_13472.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1748_13472.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1748_13472.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1748_13472.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1748_13472.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1748_13472.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1748_13472.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1748_13472.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1748_13472.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1748_13472.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1748_13472.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1748_13472.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1748_13472.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1748_13472.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1748_13472.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1748_13472.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1748_13472.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1748_13472.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1748_13472.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1748_13472.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1748_13472.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1748_13472.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1748_13472.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1748_13472.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____13473;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1748_13472.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1748_13472.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1748_13472.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1748_13472.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1748_13472.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1748_13472.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1748_13472.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1748_13472.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1748_13472.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____13474) ->
           let env1 =
             let uu___1748_13479 = env  in
             let uu____13480 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1748_13479.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1748_13479.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1748_13479.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1748_13479.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1748_13479.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1748_13479.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1748_13479.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1748_13479.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1748_13479.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1748_13479.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1748_13479.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1748_13479.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1748_13479.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1748_13479.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1748_13479.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1748_13479.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1748_13479.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1748_13479.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1748_13479.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1748_13479.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1748_13479.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1748_13479.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1748_13479.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1748_13479.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1748_13479.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1748_13479.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1748_13479.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1748_13479.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1748_13479.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1748_13479.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1748_13479.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1748_13479.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1748_13479.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1748_13479.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____13480;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1748_13479.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1748_13479.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1748_13479.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1748_13479.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1748_13479.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1748_13479.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1748_13479.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1748_13479.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1748_13479.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver )
           ->
           ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
              ();
            env)
       | FStar_Syntax_Syntax.Sig_pragma uu____13482 -> env
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13483 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____13493 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____13493) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____13494,uu____13495,uu____13496) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_13501  ->
                   match uu___5_13501 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13504 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____13506,uu____13507) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_13516  ->
                   match uu___5_13516 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13519 -> false))
           -> env
       | uu____13521 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____13590 se =
        match uu____13590 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____13643 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____13643
              then
                let uu____13646 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____13646
              else ());
             (let uu____13651 = tc_decl env1 se  in
              match uu____13651 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____13704 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____13704
                             then
                               let uu____13708 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____13708
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____13724 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____13724
                             then
                               let uu____13728 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____13728
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
                    (let uu____13745 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____13745
                     then
                       let uu____13750 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____13759 =
                                  let uu____13761 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____13761 "\n"  in
                                Prims.op_Hat s uu____13759) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____13750
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____13771 =
                       let uu____13780 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____13780
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____13822 se1 =
                            match uu____13822 with
                            | (exports1,hidden1) ->
                                let uu____13850 = for_export env3 hidden1 se1
                                   in
                                (match uu____13850 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____13771 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____14004 = acc  in
        match uu____14004 with
        | (uu____14039,uu____14040,env1,uu____14042) ->
            let r =
              let uu____14076 =
                let uu____14080 =
                  let uu____14082 = FStar_TypeChecker_Env.current_module env1
                     in
                  FStar_Ident.string_of_lid uu____14082  in
                FStar_Pervasives_Native.Some uu____14080  in
              FStar_Profiling.profile
                (fun uu____14105  -> process_one_decl acc se) uu____14076
                "FStar.TypeChecker.Tc.process_one_decl"
               in
            ((let uu____14108 = FStar_Options.profile_group_by_decls ()  in
              if uu____14108
              then
                let tag =
                  match FStar_Syntax_Util.lids_of_sigelt se with
                  | hd1::uu____14115 -> FStar_Ident.string_of_lid hd1
                  | uu____14118 ->
                      FStar_Range.string_of_range
                        (FStar_Syntax_Util.range_of_sigelt se)
                   in
                FStar_Profiling.report_and_clear tag
              else ());
             r)
         in
      let uu____14123 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____14123 with
      | (ses1,exports,env1,uu____14171) ->
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
          let uu___1848_14209 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1848_14209.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1848_14209.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1848_14209.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1848_14209.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1848_14209.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1848_14209.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1848_14209.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1848_14209.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1848_14209.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1848_14209.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___1848_14209.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1848_14209.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1848_14209.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1848_14209.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1848_14209.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___1848_14209.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1848_14209.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___1848_14209.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1848_14209.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___1848_14209.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1848_14209.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1848_14209.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1848_14209.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1848_14209.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1848_14209.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1848_14209.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1848_14209.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1848_14209.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1848_14209.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1848_14209.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1848_14209.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1848_14209.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1848_14209.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1848_14209.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___1848_14209.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___1848_14209.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1848_14209.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1848_14209.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1848_14209.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1848_14209.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1848_14209.FStar_TypeChecker_Env.strict_args_tab)
          }  in
        let check_term lid univs1 t =
          let uu____14229 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____14229 with
          | (univs2,t1) ->
              ((let uu____14237 =
                  let uu____14239 =
                    let uu____14245 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____14245  in
                  FStar_All.pipe_left uu____14239
                    (FStar_Options.Other "Exports")
                   in
                if uu____14237
                then
                  let uu____14249 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____14251 =
                    let uu____14253 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____14253
                      (FStar_String.concat ", ")
                     in
                  let uu____14270 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____14249 uu____14251 uu____14270
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____14276 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____14276 (fun a2  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____14302 =
             let uu____14304 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____14306 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____14304 uu____14306
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____14302);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14317) ->
              let uu____14326 =
                let uu____14328 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14328  in
              if uu____14326
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____14342,uu____14343) ->
              let t =
                let uu____14355 =
                  let uu____14362 =
                    let uu____14363 =
                      let uu____14378 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____14378)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____14363  in
                  FStar_Syntax_Syntax.mk uu____14362  in
                uu____14355 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____14394,uu____14395,uu____14396) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____14406 =
                let uu____14408 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14408  in
              if uu____14406 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____14416,lbs),uu____14418) ->
              let uu____14429 =
                let uu____14431 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14431  in
              if uu____14429
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
              let uu____14454 =
                let uu____14456 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14456  in
              if uu____14454
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____14477 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____14478 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14485 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14486 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____14487 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____14488 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____14495 -> ()  in
        let uu____14496 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____14496 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____14602) -> true
             | uu____14604 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____14634 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____14673 ->
                   let uu____14674 =
                     let uu____14681 =
                       let uu____14682 =
                         let uu____14697 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____14697)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____14682  in
                     FStar_Syntax_Syntax.mk uu____14681  in
                   uu____14674 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____14714,uu____14715) ->
            let s1 =
              let uu___1974_14725 = s  in
              let uu____14726 =
                let uu____14727 =
                  let uu____14734 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____14734)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____14727  in
              let uu____14735 =
                let uu____14738 =
                  let uu____14741 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____14741  in
                FStar_Syntax_Syntax.Assumption :: uu____14738  in
              {
                FStar_Syntax_Syntax.sigel = uu____14726;
                FStar_Syntax_Syntax.sigrng =
                  (uu___1974_14725.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____14735;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___1974_14725.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___1974_14725.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____14744 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____14769 lbdef =
        match uu____14769 with
        | (uvs,t) ->
            let attrs =
              let uu____14780 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____14780
              then
                let uu____14785 =
                  let uu____14786 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____14786
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____14785 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___1987_14789 = s  in
            let uu____14790 =
              let uu____14793 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____14793  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___1987_14789.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____14790;
              FStar_Syntax_Syntax.sigmeta =
                (uu___1987_14789.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____14811 -> failwith "Impossible!"  in
        let c_opt =
          let uu____14818 = FStar_Syntax_Util.is_unit t  in
          if uu____14818
          then
            let uu____14825 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____14825
          else
            (let uu____14832 =
               let uu____14833 = FStar_Syntax_Subst.compress t  in
               uu____14833.FStar_Syntax_Syntax.n  in
             match uu____14832 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____14840,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____14864 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____14876 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____14876
            then false
            else
              (let uu____14883 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____14883
               then true
               else
                 (let uu____14890 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____14890))
         in
      let extract_sigelt s =
        (let uu____14902 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____14902
         then
           let uu____14905 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____14905
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____14912 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____14932 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____14951 ->
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
                             (lid,uu____14997,uu____14998,uu____14999,uu____15000,uu____15001)
                             ->
                             ((let uu____15011 =
                                 let uu____15014 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____15014  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____15011);
                              (let uu____15063 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____15063 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____15067,uu____15068,uu____15069,uu____15070,uu____15071)
                             ->
                             ((let uu____15079 =
                                 let uu____15082 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____15082  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____15079);
                              sigelts1)
                         | uu____15131 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____15140 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15140
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____15150 =
                    let uu___2051_15151 = s  in
                    let uu____15152 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2051_15151.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2051_15151.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15152;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2051_15151.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2051_15151.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15150])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____15163 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15163
             then []
             else
               (let uu____15170 = lbs  in
                match uu____15170 with
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
                        (fun uu____15232  ->
                           match uu____15232 with
                           | (uu____15240,t,uu____15242) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____15259  ->
                             match uu____15259 with
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
                           (fun uu____15286  ->
                              match uu____15286 with
                              | (uu____15294,t,uu____15296) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____15308,uu____15309) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____15317 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____15346 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____15346) uu____15317
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____15350 =
                    let uu___2093_15351 = s  in
                    let uu____15352 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2093_15351.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2093_15351.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15352;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2093_15351.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2093_15351.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15350]
                else [])
             else
               (let uu____15359 =
                  let uu___2095_15360 = s  in
                  let uu____15361 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___2095_15360.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___2095_15360.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____15361;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___2095_15360.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___2095_15360.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____15359])
         | FStar_Syntax_Syntax.Sig_new_effect uu____15364 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15365 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____15366 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15367 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____15380 -> [s])
         in
      let uu___2107_15381 = m  in
      let uu____15382 =
        let uu____15383 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____15383 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___2107_15381.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____15382;
        FStar_Syntax_Syntax.exports =
          (uu___2107_15381.FStar_Syntax_Syntax.exports);
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
        (fun uu____15434  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____15481  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____15496 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____15496
  
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
      (let uu____15585 = FStar_Options.debug_any ()  in
       if uu____15585
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
         let uu___2132_15601 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___2132_15601.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___2132_15601.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___2132_15601.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___2132_15601.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___2132_15601.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___2132_15601.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___2132_15601.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___2132_15601.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___2132_15601.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___2132_15601.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___2132_15601.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___2132_15601.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___2132_15601.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___2132_15601.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___2132_15601.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___2132_15601.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___2132_15601.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___2132_15601.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___2132_15601.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___2132_15601.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___2132_15601.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___2132_15601.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___2132_15601.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___2132_15601.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___2132_15601.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___2132_15601.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___2132_15601.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___2132_15601.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___2132_15601.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___2132_15601.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___2132_15601.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___2132_15601.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___2132_15601.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___2132_15601.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___2132_15601.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___2132_15601.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___2132_15601.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___2132_15601.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___2132_15601.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___2132_15601.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___2132_15601.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___2132_15601.FStar_TypeChecker_Env.strict_args_tab)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____15603 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____15603 with
       | (ses,exports,env3) ->
           ((let uu___2140_15636 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___2140_15636.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___2140_15636.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___2140_15636.FStar_Syntax_Syntax.is_interface)
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
        let uu____15665 = tc_decls env decls  in
        match uu____15665 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___2149_15696 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___2149_15696.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___2149_15696.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___2149_15696.FStar_Syntax_Syntax.is_interface)
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
        let uu____15757 = tc_partial_modul env01 m  in
        match uu____15757 with
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
                (let uu____15794 = FStar_Errors.get_err_count ()  in
                 uu____15794 = Prims.int_zero)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____15805 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____15805
                then
                  let uu____15809 =
                    let uu____15811 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____15811 then "" else " (in lax mode) "  in
                  let uu____15819 =
                    let uu____15821 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____15821
                    then
                      let uu____15825 =
                        let uu____15827 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.op_Hat uu____15827 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____15825
                    else ""  in
                  let uu____15834 =
                    let uu____15836 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____15836
                    then
                      let uu____15840 =
                        let uu____15842 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____15842 "\n"  in
                      Prims.op_Hat "\nto: " uu____15840
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____15809
                    uu____15819 uu____15834
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___2175_15856 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2175_15856.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2175_15856.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2175_15856.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2175_15856.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2175_15856.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2175_15856.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2175_15856.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2175_15856.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2175_15856.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2175_15856.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2175_15856.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2175_15856.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2175_15856.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2175_15856.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2175_15856.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2175_15856.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2175_15856.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2175_15856.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2175_15856.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2175_15856.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2175_15856.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2175_15856.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2175_15856.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2175_15856.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2175_15856.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2175_15856.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2175_15856.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2175_15856.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2175_15856.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2175_15856.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2175_15856.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___2175_15856.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2175_15856.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2175_15856.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2175_15856.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2175_15856.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2175_15856.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2175_15856.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2175_15856.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2175_15856.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2175_15856.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2175_15856.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2175_15856.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let en02 =
                    let uu___2178_15858 = en01  in
                    let uu____15859 =
                      let uu____15874 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____15874, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2178_15858.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2178_15858.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2178_15858.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2178_15858.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2178_15858.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2178_15858.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2178_15858.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2178_15858.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2178_15858.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2178_15858.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2178_15858.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2178_15858.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2178_15858.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2178_15858.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2178_15858.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2178_15858.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2178_15858.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2178_15858.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2178_15858.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2178_15858.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2178_15858.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2178_15858.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2178_15858.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2178_15858.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2178_15858.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2178_15858.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2178_15858.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2178_15858.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2178_15858.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2178_15858.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2178_15858.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____15859;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2178_15858.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2178_15858.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2178_15858.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2178_15858.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2178_15858.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2178_15858.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2178_15858.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2178_15858.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2178_15858.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___2178_15858.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2178_15858.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2178_15858.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let uu____15920 =
                    let uu____15922 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____15922  in
                  if uu____15920
                  then
                    ((let uu____15926 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____15926 (fun a3  -> ()));
                     en02)
                  else en02  in
                let uu____15930 = tc_modul en0 modul_iface true  in
                match uu____15930 with
                | (modul_iface1,env) ->
                    ((let uu___2187_15943 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___2187_15943.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___2187_15943.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___2187_15943.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___2189_15947 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___2189_15947.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___2189_15947.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___2189_15947.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____15950 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____15950 FStar_Util.smap_clear);
               (let uu____15986 =
                  ((let uu____15990 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____15990) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____15993 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____15993)
                   in
                if uu____15986 then check_exports env modul exports else ());
               (let uu____15999 =
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____15999 (fun a4  -> ()));
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
        let uu____16014 =
          let uu____16016 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____16016  in
        push_context env uu____16014  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____16037 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____16048 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____16048 with | (uu____16055,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____16080 = FStar_Options.debug_any ()  in
         if uu____16080
         then
           let uu____16083 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____16083
         else ());
        (let uu____16095 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____16095
         then
           let uu____16098 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____16098
         else ());
        (let env1 =
           let uu___2219_16104 = env  in
           let uu____16105 =
             let uu____16107 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____16107  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___2219_16104.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___2219_16104.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___2219_16104.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___2219_16104.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___2219_16104.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___2219_16104.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___2219_16104.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___2219_16104.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___2219_16104.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___2219_16104.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___2219_16104.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___2219_16104.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___2219_16104.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___2219_16104.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___2219_16104.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___2219_16104.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___2219_16104.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___2219_16104.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___2219_16104.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___2219_16104.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____16105;
             FStar_TypeChecker_Env.lax_universes =
               (uu___2219_16104.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___2219_16104.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___2219_16104.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___2219_16104.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___2219_16104.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___2219_16104.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___2219_16104.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___2219_16104.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___2219_16104.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___2219_16104.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___2219_16104.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___2219_16104.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___2219_16104.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___2219_16104.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___2219_16104.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___2219_16104.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___2219_16104.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___2219_16104.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___2219_16104.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___2219_16104.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___2219_16104.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___2219_16104.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___2219_16104.FStar_TypeChecker_Env.strict_args_tab)
           }  in
         let uu____16109 = tc_modul env1 m b  in
         match uu____16109 with
         | (m1,env2) ->
             ((let uu____16121 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____16121
               then
                 let uu____16124 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____16124
               else ());
              (let uu____16130 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____16130
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
                         let uu____16168 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____16168 with
                         | (univnames1,e) ->
                             let uu___2241_16175 = lb  in
                             let uu____16176 =
                               let uu____16179 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____16179 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2241_16175.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2241_16175.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___2241_16175.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2241_16175.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16176;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2241_16175.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2241_16175.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___2243_16180 = se  in
                       let uu____16181 =
                         let uu____16182 =
                           let uu____16189 =
                             let uu____16190 = FStar_List.map update lbs  in
                             (b1, uu____16190)  in
                           (uu____16189, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____16182  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____16181;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___2243_16180.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___2243_16180.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___2243_16180.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___2243_16180.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____16198 -> se  in
                 let normalized_module =
                   let uu___2247_16200 = m1  in
                   let uu____16201 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___2247_16200.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____16201;
                     FStar_Syntax_Syntax.exports =
                       (uu___2247_16200.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___2247_16200.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____16202 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____16202
               else ());
              (m1, env2)))
  