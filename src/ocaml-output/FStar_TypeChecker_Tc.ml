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
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____239 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____239
  
let check_nogen :
  'Auu____249 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____249 Prims.list * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let t1 = tc_check_trivial_guard env t k  in
        let uu____272 =
          FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Env.Beta]
            env t1
           in
        ([], uu____272)
  
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
        let fail1 uu____308 =
          let uu____309 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____315 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____309 uu____315  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____359)::(wp,uu____361)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____390 -> fail1 ())
        | uu____391 -> fail1 ()
  
let (tc_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      (let uu____404 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____404
       then
         let uu____409 = FStar_Syntax_Print.eff_decl_to_string false ed  in
         FStar_Util.print1 "Typechecking layered effect: \n\t%s\n" uu____409
       else ());
      if
        ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
          ||
          ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
             Prims.int_zero)
      then
        (let uu____427 =
           FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname  in
         FStar_Errors.raise_error
           (FStar_Errors.Fatal_UnexpectedEffect,
             (Prims.op_Hat "Binders are not supported for layered effects ("
                (Prims.op_Hat (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                   ")"))) uu____427)
      else ();
      (let check_and_gen' comb n1 env_opt uu____467 =
         match uu____467 with
         | (us,t) ->
             let env =
               if FStar_Util.is_some env_opt
               then FStar_All.pipe_right env_opt FStar_Util.must
               else env0  in
             let uu____496 = FStar_Syntax_Subst.open_univ_vars us t  in
             (match uu____496 with
              | (us1,t1) ->
                  let uu____509 =
                    let uu____514 =
                      let uu____521 =
                        FStar_TypeChecker_Env.push_univ_vars env us1  in
                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term uu____521
                        t1
                       in
                    match uu____514 with
                    | (t2,lc,g) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (t2, (lc.FStar_TypeChecker_Common.res_typ)))
                     in
                  (match uu____509 with
                   | (t2,ty) ->
                       let uu____538 =
                         FStar_TypeChecker_Util.generalize_universes env t2
                          in
                       (match uu____538 with
                        | (g_us,t3) ->
                            let ty1 =
                              FStar_Syntax_Subst.close_univ_vars g_us ty  in
                            (if (FStar_List.length g_us) <> n1
                             then
                               (let error =
                                  let uu____561 = FStar_Util.string_of_int n1
                                     in
                                  let uu____563 =
                                    let uu____565 =
                                      FStar_All.pipe_right g_us
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____565
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format4
                                    "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                    comb uu____561 uu____563
                                   in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                    error) t3.FStar_Syntax_Syntax.pos)
                             else ();
                             (match us1 with
                              | [] -> (g_us, t3, ty1)
                              | uu____582 ->
                                  let uu____583 =
                                    ((FStar_List.length us1) =
                                       (FStar_List.length g_us))
                                      &&
                                      (FStar_List.forall2
                                         (fun u1  ->
                                            fun u2  ->
                                              let uu____590 =
                                                FStar_Syntax_Syntax.order_univ_name
                                                  u1 u2
                                                 in
                                              uu____590 = Prims.int_zero) us1
                                         g_us)
                                     in
                                  if uu____583
                                  then (g_us, t3, ty1)
                                  else
                                    (let uu____603 =
                                       let uu____609 =
                                         let uu____611 =
                                           FStar_Util.string_of_int
                                             (FStar_List.length us1)
                                            in
                                         let uu____613 =
                                           FStar_Util.string_of_int
                                             (FStar_List.length g_us)
                                            in
                                         FStar_Util.format4
                                           "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                           (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                           comb uu____611 uu____613
                                          in
                                       (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                         uu____609)
                                        in
                                     FStar_Errors.raise_error uu____603
                                       t3.FStar_Syntax_Syntax.pos))))))
          in
       let log_combinator s uu____646 =
         match uu____646 with
         | (us,t,ty) ->
             let uu____675 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                 (FStar_Options.Other "LayeredEffects")
                in
             if uu____675
             then
               let uu____680 = FStar_Syntax_Print.tscheme_to_string (us, t)
                  in
               let uu____686 = FStar_Syntax_Print.tscheme_to_string (us, ty)
                  in
               FStar_Util.print4 "Typechecked %s:%s = %s:%s\n"
                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str s uu____680
                 uu____686
             else ()
          in
       let fresh_a_and_u_a a =
         let uu____707 = FStar_Syntax_Util.type_u ()  in
         FStar_All.pipe_right uu____707
           (fun uu____724  ->
              match uu____724 with
              | (t,u) ->
                  let uu____735 =
                    let uu____736 =
                      FStar_Syntax_Syntax.gen_bv a
                        FStar_Pervasives_Native.None t
                       in
                    FStar_All.pipe_right uu____736
                      FStar_Syntax_Syntax.mk_binder
                     in
                  (uu____735, u))
          in
       let fresh_x_a x a =
         let uu____750 =
           let uu____751 =
             let uu____752 =
               FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
             FStar_All.pipe_right uu____752 FStar_Syntax_Syntax.bv_to_name
              in
           FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
             uu____751
            in
         FStar_All.pipe_right uu____750 FStar_Syntax_Syntax.mk_binder  in
       let signature =
         let r =
           (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
            in
         let uu____779 =
           check_and_gen' "signature" Prims.int_one
             FStar_Pervasives_Native.None ed.FStar_Syntax_Syntax.signature
            in
         match uu____779 with
         | (sig_us,sig_t,sig_ty) ->
             let uu____803 = FStar_Syntax_Subst.open_univ_vars sig_us sig_t
                in
             (match uu____803 with
              | (us,t) ->
                  let env = FStar_TypeChecker_Env.push_univ_vars env0 us  in
                  let uu____823 = fresh_a_and_u_a "a"  in
                  (match uu____823 with
                   | (a,u) ->
                       let rest_bs =
                         let uu____844 =
                           let uu____845 =
                             FStar_All.pipe_right a
                               FStar_Pervasives_Native.fst
                              in
                           FStar_All.pipe_right uu____845
                             FStar_Syntax_Syntax.bv_to_name
                            in
                         FStar_TypeChecker_Util.layered_effect_indices_as_binders
                           (sig_us, sig_t) u uu____844
                          in
                       let bs = a :: rest_bs  in
                       let k =
                         let uu____876 =
                           FStar_Syntax_Syntax.mk_Total
                             FStar_Syntax_Syntax.teff
                            in
                         FStar_Syntax_Util.arrow bs uu____876  in
                       let g_eq = FStar_TypeChecker_Rel.teq env t k  in
                       (FStar_TypeChecker_Rel.force_trivial_guard env g_eq;
                        (let uu____881 =
                           let uu____884 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Env.Beta] env k
                              in
                           FStar_Syntax_Subst.close_univ_vars us uu____884
                            in
                         (sig_us, uu____881, sig_ty)))))
          in
       log_combinator "signature" signature;
       (let repr =
          let r =
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.pos
             in
          let uu____911 =
            check_and_gen' "repr" Prims.int_one FStar_Pervasives_Native.None
              ed.FStar_Syntax_Syntax.repr
             in
          match uu____911 with
          | (repr_us,repr_t,repr_ty) ->
              let uu____935 =
                FStar_Syntax_Subst.open_univ_vars repr_us repr_ty  in
              (match uu____935 with
               | (us,ty) ->
                   let env = FStar_TypeChecker_Env.push_univ_vars env0 us  in
                   let uu____955 = fresh_a_and_u_a "a"  in
                   (match uu____955 with
                    | (a,u) ->
                        let rest_bs =
                          let signature_ts =
                            let uu____977 = signature  in
                            match uu____977 with
                            | (us1,t,uu____992) -> (us1, t)  in
                          let uu____1009 =
                            let uu____1010 =
                              FStar_All.pipe_right a
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____1010
                              FStar_Syntax_Syntax.bv_to_name
                             in
                          FStar_TypeChecker_Util.layered_effect_indices_as_binders
                            signature_ts u uu____1009
                           in
                        let bs = a :: rest_bs  in
                        let k =
                          let uu____1037 =
                            let uu____1040 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_right uu____1040
                              (fun uu____1052  ->
                                 match uu____1052 with
                                 | (t,u1) ->
                                     FStar_Syntax_Syntax.mk_Total' t
                                       (FStar_Pervasives_Native.Some u1))
                             in
                          FStar_Syntax_Util.arrow bs uu____1037  in
                        let g = FStar_TypeChecker_Rel.teq env ty k  in
                        (FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (let uu____1061 =
                            let uu____1064 =
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Env.Beta] env k
                               in
                            FStar_Syntax_Subst.close_univ_vars us uu____1064
                             in
                          (repr_us, repr_t, uu____1061)))))
           in
        log_combinator "repr" repr;
        (let fresh_repr r env u a_tm =
           let signature_ts =
             let uu____1099 = signature  in
             match uu____1099 with | (us,t,uu____1114) -> (us, t)  in
           let repr_ts =
             let uu____1132 = repr  in
             match uu____1132 with | (us,t,uu____1147) -> (us, t)  in
           FStar_TypeChecker_Util.fresh_layered_effect_repr env r
             ed.FStar_Syntax_Syntax.mname signature_ts repr_ts u a_tm
            in
         let return_repr =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
              in
           let uu____1182 =
             check_and_gen' "return_repr" Prims.int_one
               FStar_Pervasives_Native.None
               ed.FStar_Syntax_Syntax.return_repr
              in
           match uu____1182 with
           | (ret_us,ret_t,ret_ty) ->
               let uu____1206 =
                 FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
               (match uu____1206 with
                | (us,ty) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                       in
                    let uu____1226 = fresh_a_and_u_a "a"  in
                    (match uu____1226 with
                     | (a,u_a) ->
                         let rest_bs =
                           let uu____1255 =
                             let uu____1256 = FStar_Syntax_Subst.compress ty
                                in
                             uu____1256.FStar_Syntax_Syntax.n  in
                           match uu____1255 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1268)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____1296 =
                                 FStar_Syntax_Subst.open_binders bs  in
                               (match uu____1296 with
                                | (a',uu____1306)::bs1 ->
                                    let uu____1326 =
                                      FStar_List.splitAt
                                        ((FStar_List.length bs1) -
                                           Prims.int_one) bs1
                                       in
                                    (match uu____1326 with
                                     | (bs2,uu____1369) ->
                                         let substs =
                                           let uu____1405 =
                                             let uu____1406 =
                                               let uu____1413 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   (FStar_Pervasives_Native.fst
                                                      a)
                                                  in
                                               (a', uu____1413)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____1406
                                              in
                                           [uu____1405]  in
                                         FStar_Syntax_Subst.subst_binders
                                           substs bs2)
                                | uu____1420 -> failwith "Impossible!")
                           | uu____1430 ->
                               FStar_Errors.raise_error
                                 (FStar_Errors.Fatal_UnexpectedEffect, "") r
                            in
                         let bs =
                           let uu____1450 =
                             let uu____1459 =
                               let uu____1468 = fresh_x_a "x" a  in
                               [uu____1468]  in
                             FStar_List.append rest_bs uu____1459  in
                           a :: uu____1450  in
                         let uu____1500 =
                           let uu____1505 =
                             FStar_TypeChecker_Env.push_binders env bs  in
                           let uu____1506 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.fst a)
                               FStar_Syntax_Syntax.bv_to_name
                              in
                           fresh_repr r uu____1505 u_a uu____1506  in
                         (match uu____1500 with
                          | (repr1,g) ->
                              let k =
                                let uu____1526 =
                                  FStar_Syntax_Syntax.mk_Total' repr1
                                    (FStar_Pervasives_Native.Some u_a)
                                   in
                                FStar_Syntax_Util.arrow bs uu____1526  in
                              let g_eq = FStar_TypeChecker_Rel.teq env ty k
                                 in
                              ((let uu____1531 =
                                  FStar_TypeChecker_Env.conj_guard g g_eq  in
                                FStar_TypeChecker_Rel.force_trivial_guard env
                                  uu____1531);
                               (let uu____1532 =
                                  let uu____1535 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env k
                                     in
                                  FStar_Syntax_Subst.close_univ_vars us
                                    uu____1535
                                   in
                                (ret_us, ret_t, uu____1532))))))
            in
         log_combinator "return_repr" return_repr;
         (let bind_repr =
            let r =
              (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
               in
            let uu____1562 =
              check_and_gen' "bind_repr" (Prims.of_int (2))
                FStar_Pervasives_Native.None ed.FStar_Syntax_Syntax.bind_repr
               in
            match uu____1562 with
            | (bind_us,bind_t,bind_ty) ->
                let uu____1586 =
                  FStar_Syntax_Subst.open_univ_vars bind_us bind_ty  in
                (match uu____1586 with
                 | (us,ty) ->
                     let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                        in
                     let uu____1606 = fresh_a_and_u_a "a"  in
                     (match uu____1606 with
                      | (a,u_a) ->
                          let uu____1626 = fresh_a_and_u_a "b"  in
                          (match uu____1626 with
                           | (b,u_b) ->
                               let rest_bs =
                                 let uu____1655 =
                                   let uu____1656 =
                                     FStar_Syntax_Subst.compress ty  in
                                   uu____1656.FStar_Syntax_Syntax.n  in
                                 match uu____1655 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____1668) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (4))
                                     ->
                                     let uu____1696 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____1696 with
                                      | (a',uu____1706)::(b',uu____1708)::bs1
                                          ->
                                          let uu____1738 =
                                            FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 (Prims.of_int (2))) bs1
                                             in
                                          (match uu____1738 with
                                           | (bs2,uu____1781) ->
                                               let substs =
                                                 let uu____1817 =
                                                   let uu____1818 =
                                                     let uu____1825 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a)
                                                        in
                                                     (a', uu____1825)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____1818
                                                    in
                                                 let uu____1832 =
                                                   let uu____1835 =
                                                     let uu____1836 =
                                                       let uu____1843 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              b)
                                                          in
                                                       (b', uu____1843)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____1836
                                                      in
                                                   [uu____1835]  in
                                                 uu____1817 :: uu____1832  in
                                               FStar_Syntax_Subst.subst_binders
                                                 substs bs2)
                                      | uu____1850 -> failwith "Impossible!")
                                 | uu____1860 ->
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_UnexpectedEffect,
                                         "") r
                                  in
                               let bs = a :: b :: rest_bs  in
                               let uu____1892 =
                                 let uu____1903 =
                                   let uu____1908 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____1909 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____1908 u_a uu____1909  in
                                 match uu____1903 with
                                 | (repr1,g) ->
                                     let uu____1924 =
                                       let uu____1931 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None repr1
                                          in
                                       FStar_All.pipe_right uu____1931
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____1924, g)
                                  in
                               (match uu____1892 with
                                | (f,g_f) ->
                                    let uu____1971 =
                                      let x_a = fresh_x_a "x" a  in
                                      let uu____1984 =
                                        let uu____1989 =
                                          FStar_TypeChecker_Env.push_binders
                                            env (FStar_List.append bs [x_a])
                                           in
                                        let uu____2008 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst b)
                                            FStar_Syntax_Syntax.bv_to_name
                                           in
                                        fresh_repr r uu____1989 u_b
                                          uu____2008
                                         in
                                      match uu____1984 with
                                      | (repr1,g) ->
                                          let uu____2023 =
                                            let uu____2030 =
                                              let uu____2031 =
                                                let uu____2032 =
                                                  FStar_Syntax_Syntax.mk_Total'
                                                    repr1
                                                    (FStar_Pervasives_Native.Some
                                                       u_b)
                                                   in
                                                FStar_Syntax_Util.arrow 
                                                  [x_a] uu____2032
                                                 in
                                              FStar_Syntax_Syntax.gen_bv "g"
                                                FStar_Pervasives_Native.None
                                                uu____2031
                                               in
                                            FStar_All.pipe_right uu____2030
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          (uu____2023, g)
                                       in
                                    (match uu____1971 with
                                     | (g,g_g) ->
                                         let uu____2086 =
                                           let uu____2091 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____2092 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst b)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____2091 u_b
                                             uu____2092
                                            in
                                         (match uu____2086 with
                                          | (repr1,g_repr) ->
                                              let k =
                                                let uu____2112 =
                                                  FStar_Syntax_Syntax.mk_Total'
                                                    repr1
                                                    (FStar_Pervasives_Native.Some
                                                       u_b)
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  (FStar_List.append bs
                                                     [f; g]) uu____2112
                                                 in
                                              let g_eq =
                                                FStar_TypeChecker_Rel.teq env
                                                  ty k
                                                 in
                                              (FStar_List.iter
                                                 (FStar_TypeChecker_Rel.force_trivial_guard
                                                    env)
                                                 [g_f; g_g; g_repr; g_eq];
                                               (let uu____2141 =
                                                  let uu____2144 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Beta]
                                                      env k
                                                     in
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    bind_us uu____2144
                                                   in
                                                (bind_us, bind_t, uu____2141)))))))))
             in
          log_combinator "bind_repr" bind_repr;
          (let stronger_repr =
             let stronger_repr =
               FStar_All.pipe_right ed.FStar_Syntax_Syntax.stronger_repr
                 FStar_Util.must
                in
             let r =
               (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                in
             let uu____2186 =
               check_and_gen' "stronger_repr" Prims.int_one
                 FStar_Pervasives_Native.None stronger_repr
                in
             match uu____2186 with
             | (stronger_us,stronger_t,stronger_ty) ->
                 ((let uu____2211 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                       (FStar_Options.Other "LayeredEffects")
                      in
                   if uu____2211
                   then
                     let uu____2216 =
                       FStar_Syntax_Print.tscheme_to_string
                         (stronger_us, stronger_t)
                        in
                     let uu____2222 =
                       FStar_Syntax_Print.tscheme_to_string
                         (stronger_us, stronger_ty)
                        in
                     FStar_Util.print2
                       "stronger combinator typechecked with term: %s and type: %s\n"
                       uu____2216 uu____2222
                   else ());
                  (let uu____2231 =
                     FStar_Syntax_Subst.open_univ_vars stronger_us
                       stronger_ty
                      in
                   match uu____2231 with
                   | (us,ty) ->
                       let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                          in
                       let uu____2251 = fresh_a_and_u_a "a"  in
                       (match uu____2251 with
                        | (a,u) ->
                            let f_is_bs =
                              let signature_ts =
                                let uu____2273 = signature  in
                                match uu____2273 with
                                | (us1,t,uu____2288) -> (us1, t)  in
                              let uu____2305 =
                                let uu____2306 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____2306
                                  FStar_Syntax_Syntax.bv_to_name
                                 in
                              FStar_TypeChecker_Util.layered_effect_indices_as_binders
                                signature_ts u uu____2305
                               in
                            let g_is_bs =
                              let signature_ts =
                                let uu____2317 = signature  in
                                match uu____2317 with
                                | (us1,t,uu____2332) -> (us1, t)  in
                              let uu____2349 =
                                let uu____2350 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____2350
                                  FStar_Syntax_Syntax.bv_to_name
                                 in
                              FStar_TypeChecker_Util.layered_effect_indices_as_binders
                                signature_ts u uu____2349
                               in
                            let f_b =
                              let repr_ts =
                                let uu____2367 = repr  in
                                match uu____2367 with
                                | (us1,t,uu____2382) -> (us1, t)  in
                              let uu____2399 =
                                FStar_TypeChecker_Env.inst_tscheme_with
                                  repr_ts [u]
                                 in
                              match uu____2399 with
                              | (uu____2410,repr1) ->
                                  let repr2 =
                                    let uu____2415 =
                                      let uu____2420 =
                                        let uu____2421 =
                                          let uu____2424 =
                                            FStar_All.pipe_right (a ::
                                              f_is_bs)
                                              (FStar_List.map
                                                 FStar_Pervasives_Native.fst)
                                             in
                                          FStar_All.pipe_right uu____2424
                                            (FStar_List.map
                                               FStar_Syntax_Syntax.bv_to_name)
                                           in
                                        FStar_All.pipe_right uu____2421
                                          (FStar_List.map
                                             FStar_Syntax_Syntax.as_arg)
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app repr1
                                        uu____2420
                                       in
                                    uu____2415 FStar_Pervasives_Native.None r
                                     in
                                  let uu____2457 =
                                    FStar_Syntax_Syntax.gen_bv "f"
                                      FStar_Pervasives_Native.None repr2
                                     in
                                  FStar_All.pipe_right uu____2457
                                    FStar_Syntax_Syntax.mk_binder
                               in
                            let ret_t =
                              let repr_ts =
                                let uu____2469 = repr  in
                                match uu____2469 with
                                | (us1,t,uu____2484) -> (us1, t)  in
                              let uu____2501 =
                                FStar_TypeChecker_Env.inst_tscheme_with
                                  repr_ts [u]
                                 in
                              match uu____2501 with
                              | (uu____2508,repr1) ->
                                  let uu____2510 =
                                    let uu____2515 =
                                      let uu____2516 =
                                        let uu____2519 =
                                          FStar_All.pipe_right (a :: g_is_bs)
                                            (FStar_List.map
                                               FStar_Pervasives_Native.fst)
                                           in
                                        FStar_All.pipe_right uu____2519
                                          (FStar_List.map
                                             FStar_Syntax_Syntax.bv_to_name)
                                         in
                                      FStar_All.pipe_right uu____2516
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.as_arg)
                                       in
                                    FStar_Syntax_Syntax.mk_Tm_app repr1
                                      uu____2515
                                     in
                                  uu____2510 FStar_Pervasives_Native.None r
                               in
                            let pure_wp_t =
                              let pure_wp_ts =
                                let uu____2554 =
                                  FStar_TypeChecker_Env.lookup_definition
                                    [FStar_TypeChecker_Env.NoDelta] env
                                    FStar_Parser_Const.pure_wp_lid
                                   in
                                FStar_All.pipe_right uu____2554
                                  FStar_Util.must
                                 in
                              let uu____2571 =
                                FStar_TypeChecker_Env.inst_tscheme pure_wp_ts
                                 in
                              match uu____2571 with
                              | (uu____2576,pure_wp_t) ->
                                  let uu____2578 =
                                    let uu____2583 =
                                      let uu____2584 =
                                        FStar_All.pipe_right ret_t
                                          FStar_Syntax_Syntax.as_arg
                                         in
                                      [uu____2584]  in
                                    FStar_Syntax_Syntax.mk_Tm_app pure_wp_t
                                      uu____2583
                                     in
                                  uu____2578 FStar_Pervasives_Native.None r
                               in
                            let uu____2617 =
                              let uu____2630 =
                                FStar_TypeChecker_Env.push_binders env (a ::
                                  (FStar_List.append f_is_bs g_is_bs))
                                 in
                              FStar_TypeChecker_Util.new_implicit_var "" r
                                uu____2630 pure_wp_t
                               in
                            (match uu____2617 with
                             | (pure_wp_uvar,uu____2657,g_pure_wp_uvar) ->
                                 let c =
                                   let uu____2672 =
                                     let uu____2673 =
                                       let uu____2674 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       [uu____2674]  in
                                     let uu____2675 =
                                       let uu____2686 =
                                         FStar_All.pipe_right pure_wp_uvar
                                           FStar_Syntax_Syntax.as_arg
                                          in
                                       [uu____2686]  in
                                     {
                                       FStar_Syntax_Syntax.comp_univs =
                                         uu____2673;
                                       FStar_Syntax_Syntax.effect_name =
                                         FStar_Parser_Const.effect_PURE_lid;
                                       FStar_Syntax_Syntax.result_typ = ret_t;
                                       FStar_Syntax_Syntax.effect_args =
                                         uu____2675;
                                       FStar_Syntax_Syntax.flags = []
                                     }  in
                                   FStar_Syntax_Syntax.mk_Comp uu____2672  in
                                 let k =
                                   FStar_Syntax_Util.arrow (a ::
                                     (FStar_List.append f_is_bs
                                        (FStar_List.append g_is_bs [f_b]))) c
                                    in
                                 ((let uu____2753 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "LayeredEffects")
                                      in
                                   if uu____2753
                                   then
                                     let uu____2758 =
                                       FStar_Syntax_Print.term_to_string k
                                        in
                                     FStar_Util.print1
                                       "Expected type before unification: %s\n"
                                       uu____2758
                                   else ());
                                  (let g = FStar_TypeChecker_Rel.teq env ty k
                                      in
                                   (let uu____2765 =
                                      FStar_TypeChecker_Env.conj_guard
                                        g_pure_wp_uvar g
                                       in
                                    FStar_TypeChecker_Rel.force_trivial_guard
                                      env uu____2765);
                                   (let k1 =
                                      let k1 =
                                        FStar_TypeChecker_Normalize.remove_uvar_solutions
                                          env k
                                         in
                                      let uu____2768 =
                                        let uu____2769 =
                                          FStar_Syntax_Subst.compress k1  in
                                        uu____2769.FStar_Syntax_Syntax.n  in
                                      match uu____2768 with
                                      | FStar_Syntax_Syntax.Tm_arrow 
                                          (bs,c1) ->
                                          let uu____2794 =
                                            FStar_Syntax_Subst.open_comp bs
                                              c1
                                             in
                                          (match uu____2794 with
                                           | (bs1,c2) ->
                                               let uu____2801 =
                                                 let uu____2808 =
                                                   FStar_All.pipe_right c2
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2808
                                                   FStar_Syntax_Util.destruct_comp
                                                  in
                                               (match uu____2801 with
                                                | (u1,uu____2816,wp) ->
                                                    let trivial_post =
                                                      let ts =
                                                        let uu____2820 =
                                                          FStar_TypeChecker_Env.lookup_definition
                                                            [FStar_TypeChecker_Env.NoDelta]
                                                            env
                                                            FStar_Parser_Const.trivial_pure_post_lid
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____2820
                                                          FStar_Util.must
                                                         in
                                                      let uu____2837 =
                                                        FStar_TypeChecker_Env.inst_tscheme_with
                                                          ts [u1]
                                                         in
                                                      match uu____2837 with
                                                      | (uu____2842,t) ->
                                                          let uu____2844 =
                                                            let uu____2849 =
                                                              let uu____2850
                                                                =
                                                                FStar_All.pipe_right
                                                                  ret_t
                                                                  FStar_Syntax_Syntax.as_arg
                                                                 in
                                                              [uu____2850]
                                                               in
                                                            FStar_Syntax_Syntax.mk_Tm_app
                                                              t uu____2849
                                                             in
                                                          uu____2844
                                                            FStar_Pervasives_Native.None
                                                            r
                                                       in
                                                    let fml =
                                                      let uu____2886 =
                                                        let uu____2891 =
                                                          let uu____2892 =
                                                            FStar_All.pipe_right
                                                              trivial_post
                                                              FStar_Syntax_Syntax.as_arg
                                                             in
                                                          [uu____2892]  in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          wp uu____2891
                                                         in
                                                      uu____2886
                                                        FStar_Pervasives_Native.None
                                                        r
                                                       in
                                                    let uu____2925 =
                                                      FStar_Syntax_Syntax.mk_Total'
                                                        fml
                                                        (FStar_Pervasives_Native.Some
                                                           FStar_Syntax_Syntax.U_zero)
                                                       in
                                                    FStar_Syntax_Util.arrow
                                                      bs1 uu____2925))
                                      | uu____2928 -> failwith "Impossible!"
                                       in
                                    let uu____2930 =
                                      let uu____2933 =
                                        FStar_All.pipe_right k1
                                          (FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta;
                                             FStar_TypeChecker_Env.Eager_unfolding]
                                             env)
                                         in
                                      FStar_All.pipe_right uu____2933
                                        (FStar_Syntax_Subst.close_univ_vars
                                           stronger_us)
                                       in
                                    (stronger_us, stronger_t, uu____2930))))))))
              in
           log_combinator "stronger_repr" stronger_repr;
           (let tc_action env act =
              let r =
                (act.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                 in
              if
                (FStar_List.length act.FStar_Syntax_Syntax.action_params) <>
                  Prims.int_zero
              then
                failwith
                  "tc_layered_eff_decl: expected action_params to be empty"
              else ();
              (let uu____2969 =
                 let uu____2974 =
                   FStar_Syntax_Subst.univ_var_opening
                     act.FStar_Syntax_Syntax.action_univs
                    in
                 match uu____2974 with
                 | (usubst,us) ->
                     let uu____2997 =
                       FStar_TypeChecker_Env.push_univ_vars env us  in
                     let uu____2998 =
                       let uu___363_2999 = act  in
                       let uu____3000 =
                         FStar_Syntax_Subst.subst usubst
                           act.FStar_Syntax_Syntax.action_defn
                          in
                       let uu____3001 =
                         FStar_Syntax_Subst.subst usubst
                           act.FStar_Syntax_Syntax.action_typ
                          in
                       {
                         FStar_Syntax_Syntax.action_name =
                           (uu___363_2999.FStar_Syntax_Syntax.action_name);
                         FStar_Syntax_Syntax.action_unqualified_name =
                           (uu___363_2999.FStar_Syntax_Syntax.action_unqualified_name);
                         FStar_Syntax_Syntax.action_univs = us;
                         FStar_Syntax_Syntax.action_params =
                           (uu___363_2999.FStar_Syntax_Syntax.action_params);
                         FStar_Syntax_Syntax.action_defn = uu____3000;
                         FStar_Syntax_Syntax.action_typ = uu____3001
                       }  in
                     (uu____2997, uu____2998)
                  in
               match uu____2969 with
               | (env1,act1) ->
                   let act_typ =
                     let uu____3005 =
                       let uu____3006 =
                         FStar_Syntax_Subst.compress
                           act1.FStar_Syntax_Syntax.action_typ
                          in
                       uu____3006.FStar_Syntax_Syntax.n  in
                     match uu____3005 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                         let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
                         let uu____3032 =
                           FStar_Ident.lid_equals
                             ct.FStar_Syntax_Syntax.effect_name
                             ed.FStar_Syntax_Syntax.mname
                            in
                         if uu____3032
                         then
                           let repr_ts =
                             let uu____3036 = repr  in
                             match uu____3036 with
                             | (us,t,uu____3051) -> (us, t)  in
                           let repr1 =
                             let uu____3069 =
                               FStar_TypeChecker_Env.inst_tscheme_with
                                 repr_ts ct.FStar_Syntax_Syntax.comp_univs
                                in
                             FStar_All.pipe_right uu____3069
                               FStar_Pervasives_Native.snd
                              in
                           let c1 =
                             let uu____3081 =
                               let uu____3082 =
                                 let uu____3087 =
                                   let uu____3088 =
                                     FStar_Syntax_Syntax.as_arg
                                       ct.FStar_Syntax_Syntax.result_typ
                                      in
                                   uu____3088 ::
                                     (ct.FStar_Syntax_Syntax.effect_args)
                                    in
                                 FStar_Syntax_Syntax.mk_Tm_app repr1
                                   uu____3087
                                  in
                               uu____3082 FStar_Pervasives_Native.None r  in
                             FStar_All.pipe_right uu____3081
                               FStar_Syntax_Syntax.mk_Total
                              in
                           FStar_Syntax_Util.arrow bs c1
                         else act1.FStar_Syntax_Syntax.action_typ
                     | uu____3109 -> act1.FStar_Syntax_Syntax.action_typ  in
                   let uu____3110 =
                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                       act_typ
                      in
                   (match uu____3110 with
                    | (act_typ1,uu____3118,g_t) ->
                        let uu____3120 =
                          let uu____3127 =
                            let uu___387_3128 =
                              FStar_TypeChecker_Env.set_expected_typ env1
                                act_typ1
                               in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___387_3128.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___387_3128.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___387_3128.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___387_3128.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___387_3128.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___387_3128.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___387_3128.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___387_3128.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___387_3128.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___387_3128.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___387_3128.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp = false;
                              FStar_TypeChecker_Env.effects =
                                (uu___387_3128.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___387_3128.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___387_3128.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___387_3128.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___387_3128.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___387_3128.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___387_3128.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___387_3128.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax =
                                (uu___387_3128.FStar_TypeChecker_Env.lax);
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___387_3128.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___387_3128.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___387_3128.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___387_3128.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___387_3128.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___387_3128.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___387_3128.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___387_3128.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___387_3128.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___387_3128.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___387_3128.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___387_3128.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___387_3128.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___387_3128.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___387_3128.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___387_3128.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___387_3128.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___387_3128.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___387_3128.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___387_3128.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___387_3128.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___387_3128.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___387_3128.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___387_3128.FStar_TypeChecker_Env.strict_args_tab)
                            }  in
                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                            uu____3127 act1.FStar_Syntax_Syntax.action_defn
                           in
                        (match uu____3120 with
                         | (act_defn,uu____3131,g_d) ->
                             ((let uu____3134 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env1)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____3134
                               then
                                 let uu____3139 =
                                   FStar_Syntax_Print.term_to_string act_defn
                                    in
                                 let uu____3141 =
                                   FStar_Syntax_Print.term_to_string act_typ1
                                    in
                                 FStar_Util.print2
                                   "Typechecked action definition: %s and action type: %s\n"
                                   uu____3139 uu____3141
                               else ());
                              (let uu____3146 =
                                 let act_typ2 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Beta] env1
                                     act_typ1
                                    in
                                 let uu____3154 =
                                   let uu____3155 =
                                     FStar_Syntax_Subst.compress act_typ2  in
                                   uu____3155.FStar_Syntax_Syntax.n  in
                                 match uu____3154 with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                     let bs1 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     let env2 =
                                       FStar_TypeChecker_Env.push_binders
                                         env1 bs1
                                        in
                                     let uu____3188 =
                                       FStar_Syntax_Util.type_u ()  in
                                     (match uu____3188 with
                                      | (t,u) ->
                                          let uu____3201 =
                                            FStar_TypeChecker_Util.new_implicit_var
                                              "" r env2 t
                                             in
                                          (match uu____3201 with
                                           | (a_tm,uu____3222,g_tm) ->
                                               let uu____3236 =
                                                 fresh_repr r env2 u a_tm  in
                                               (match uu____3236 with
                                                | (repr1,g) ->
                                                    let uu____3249 =
                                                      let uu____3252 =
                                                        let uu____3255 =
                                                          let uu____3258 =
                                                            FStar_TypeChecker_Env.new_u_univ
                                                              ()
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____3258
                                                            (fun _3261  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _3261)
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total'
                                                          repr1 uu____3255
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____3252
                                                       in
                                                    let uu____3262 =
                                                      FStar_TypeChecker_Env.conj_guard
                                                        g g_tm
                                                       in
                                                    (uu____3249, uu____3262))))
                                 | uu____3265 ->
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                         "") r
                                  in
                               match uu____3146 with
                               | (k,g_k) ->
                                   ((let uu____3281 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other
                                            "LayeredEffects")
                                        in
                                     if uu____3281
                                     then
                                       let uu____3286 =
                                         FStar_Syntax_Print.term_to_string k
                                          in
                                       FStar_Util.print1
                                         "Expected action type: %s\n"
                                         uu____3286
                                     else ());
                                    (let g =
                                       FStar_TypeChecker_Rel.teq env1
                                         act_typ1 k
                                        in
                                     FStar_List.iter
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1) [g_t; g_d; g_k; g];
                                     (let uu____3294 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____3294
                                      then
                                        let uu____3299 =
                                          FStar_Syntax_Print.term_to_string k
                                           in
                                        FStar_Util.print1
                                          "Expected action type after unification: %s\n"
                                          uu____3299
                                      else ());
                                     (let act_typ2 =
                                        let repr_args t =
                                          let uu____3323 =
                                            let uu____3324 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____3324.FStar_Syntax_Syntax.n
                                             in
                                          match uu____3323 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (head1,a::is) ->
                                              let uu____3376 =
                                                let uu____3377 =
                                                  FStar_Syntax_Subst.compress
                                                    head1
                                                   in
                                                uu____3377.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____3376 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (uu____3386,us) ->
                                                   (us,
                                                     (FStar_Pervasives_Native.fst
                                                        a), is)
                                               | uu____3396 ->
                                                   failwith "Impossible!")
                                          | uu____3404 ->
                                              failwith "Impossible!"
                                           in
                                        let k1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Env.Beta] env1
                                            k
                                           in
                                        let uu____3413 =
                                          let uu____3414 =
                                            FStar_Syntax_Subst.compress k1
                                             in
                                          uu____3414.FStar_Syntax_Syntax.n
                                           in
                                        match uu____3413 with
                                        | FStar_Syntax_Syntax.Tm_arrow 
                                            (bs,c) ->
                                            let uu____3439 =
                                              FStar_Syntax_Subst.open_comp bs
                                                c
                                               in
                                            (match uu____3439 with
                                             | (bs1,c1) ->
                                                 let uu____3446 =
                                                   repr_args
                                                     (FStar_Syntax_Util.comp_result
                                                        c1)
                                                    in
                                                 (match uu____3446 with
                                                  | (us,a,is) ->
                                                      let ct =
                                                        {
                                                          FStar_Syntax_Syntax.comp_univs
                                                            = us;
                                                          FStar_Syntax_Syntax.effect_name
                                                            =
                                                            (ed.FStar_Syntax_Syntax.mname);
                                                          FStar_Syntax_Syntax.result_typ
                                                            = a;
                                                          FStar_Syntax_Syntax.effect_args
                                                            = is;
                                                          FStar_Syntax_Syntax.flags
                                                            = []
                                                        }  in
                                                      let uu____3457 =
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          ct
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____3457))
                                        | uu____3460 ->
                                            failwith "Impossible!"
                                         in
                                      (let uu____3463 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____3463
                                       then
                                         let uu____3468 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ2
                                            in
                                         FStar_Util.print1
                                           "Action type after injecting it into the monad: %s\n"
                                           uu____3468
                                       else ());
                                      (let act2 =
                                         if
                                           act1.FStar_Syntax_Syntax.action_univs
                                             = []
                                         then
                                           let uu____3477 =
                                             FStar_TypeChecker_Util.generalize_universes
                                               env1 act_defn
                                              in
                                           match uu____3477 with
                                           | (us,act_defn1) ->
                                               let uu___457_3488 = act1  in
                                               let uu____3489 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   us act_typ2
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___457_3488.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___457_3488.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = us;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___457_3488.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = act_defn1;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = uu____3489
                                               }
                                         else
                                           (let uu___459_3492 = act1  in
                                            let uu____3493 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                act1.FStar_Syntax_Syntax.action_univs
                                                act_defn
                                               in
                                            let uu____3494 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                act1.FStar_Syntax_Syntax.action_univs
                                                act_typ2
                                               in
                                            {
                                              FStar_Syntax_Syntax.action_name
                                                =
                                                (uu___459_3492.FStar_Syntax_Syntax.action_name);
                                              FStar_Syntax_Syntax.action_unqualified_name
                                                =
                                                (uu___459_3492.FStar_Syntax_Syntax.action_unqualified_name);
                                              FStar_Syntax_Syntax.action_univs
                                                =
                                                (uu___459_3492.FStar_Syntax_Syntax.action_univs);
                                              FStar_Syntax_Syntax.action_params
                                                =
                                                (uu___459_3492.FStar_Syntax_Syntax.action_params);
                                              FStar_Syntax_Syntax.action_defn
                                                = uu____3493;
                                              FStar_Syntax_Syntax.action_typ
                                                = uu____3494
                                            })
                                          in
                                       act2)))))))))
               in
            let fst1 uu____3514 =
              match uu____3514 with | (a,uu____3530,uu____3531) -> a  in
            let snd1 uu____3563 =
              match uu____3563 with | (uu____3578,b,uu____3580) -> b  in
            let thd uu____3612 =
              match uu____3612 with | (uu____3627,uu____3628,c) -> c  in
            let uu___477_3642 = ed  in
            let uu____3643 =
              FStar_All.pipe_right
                ((fst1 stronger_repr), (snd1 stronger_repr))
                (fun _3652  -> FStar_Pervasives_Native.Some _3652)
               in
            let uu____3653 =
              FStar_List.map (tc_action env0) ed.FStar_Syntax_Syntax.actions
               in
            {
              FStar_Syntax_Syntax.is_layered =
                (uu___477_3642.FStar_Syntax_Syntax.is_layered);
              FStar_Syntax_Syntax.cattributes =
                (uu___477_3642.FStar_Syntax_Syntax.cattributes);
              FStar_Syntax_Syntax.mname =
                (uu___477_3642.FStar_Syntax_Syntax.mname);
              FStar_Syntax_Syntax.univs =
                (uu___477_3642.FStar_Syntax_Syntax.univs);
              FStar_Syntax_Syntax.binders =
                (uu___477_3642.FStar_Syntax_Syntax.binders);
              FStar_Syntax_Syntax.signature =
                ((fst1 signature), (snd1 signature));
              FStar_Syntax_Syntax.ret_wp =
                ((fst1 return_repr), (thd return_repr));
              FStar_Syntax_Syntax.bind_wp =
                ((fst1 bind_repr), (thd bind_repr));
              FStar_Syntax_Syntax.stronger =
                ((fst1 stronger_repr), (thd stronger_repr));
              FStar_Syntax_Syntax.match_wps =
                (uu___477_3642.FStar_Syntax_Syntax.match_wps);
              FStar_Syntax_Syntax.trivial =
                (uu___477_3642.FStar_Syntax_Syntax.trivial);
              FStar_Syntax_Syntax.repr = ((fst1 repr), (snd1 repr));
              FStar_Syntax_Syntax.return_repr =
                ((fst1 return_repr), (snd1 return_repr));
              FStar_Syntax_Syntax.bind_repr =
                ((fst1 bind_repr), (snd1 bind_repr));
              FStar_Syntax_Syntax.stronger_repr = uu____3643;
              FStar_Syntax_Syntax.actions = uu____3653;
              FStar_Syntax_Syntax.eff_attrs =
                (uu___477_3642.FStar_Syntax_Syntax.eff_attrs)
            }))))))
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____3696 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____3696
       then
         let uu____3701 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____3701
       else ());
      (let uu____3706 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____3706 with
       | (us,lift) ->
           let r = lift.FStar_Syntax_Syntax.pos  in
           (if (FStar_List.length us) <> Prims.int_zero
            then
              (let uu____3740 =
                 let uu____3742 = FStar_Syntax_Print.sub_eff_to_string sub1
                    in
                 Prims.op_Hat
                   "Unexpected number of universes in typechecking %s"
                   uu____3742
                  in
               failwith uu____3740)
            else ();
            (let uu____3747 =
               FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env0 lift  in
             match uu____3747 with
             | (lift1,lc,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env0 g;
                  (let lift_ty =
                     FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                       (FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Beta] env0)
                      in
                   (let uu____3764 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                        (FStar_Options.Other "LayeredEffects")
                       in
                    if uu____3764
                    then
                      let uu____3769 =
                        FStar_Syntax_Print.term_to_string lift1  in
                      let uu____3771 =
                        FStar_Syntax_Print.term_to_string lift_ty  in
                      FStar_Util.print2
                        "Typechecked lift: %s and lift_ty: %s\n" uu____3769
                        uu____3771
                    else ());
                   (let uu____3776 =
                      let uu____3783 =
                        let uu____3788 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____3788
                          (fun uu____3805  ->
                             match uu____3805 with
                             | (t,u) ->
                                 let uu____3816 =
                                   let uu____3817 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t
                                      in
                                   FStar_All.pipe_right uu____3817
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____3816, u))
                         in
                      match uu____3783 with
                      | (a,u_a) ->
                          let uu____3827 =
                            let uu____3834 =
                              FStar_TypeChecker_Env.lookup_effect_lid env0
                                sub1.FStar_Syntax_Syntax.source
                               in
                            monad_signature env0
                              sub1.FStar_Syntax_Syntax.source uu____3834
                             in
                          (match uu____3827 with
                           | (a',wp_sort_a') ->
                               let src_wp_sort_a =
                                 let uu____3848 =
                                   let uu____3851 =
                                     let uu____3852 =
                                       let uu____3859 =
                                         let uu____3862 =
                                           FStar_All.pipe_right a
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_All.pipe_right uu____3862
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       (a', uu____3859)  in
                                     FStar_Syntax_Syntax.NT uu____3852  in
                                   [uu____3851]  in
                                 FStar_Syntax_Subst.subst uu____3848
                                   wp_sort_a'
                                  in
                               let wp =
                                 let uu____3882 =
                                   FStar_Syntax_Syntax.gen_bv "wp"
                                     FStar_Pervasives_Native.None
                                     src_wp_sort_a
                                    in
                                 FStar_All.pipe_right uu____3882
                                   FStar_Syntax_Syntax.mk_binder
                                  in
                               let rest_bs =
                                 let uu____3899 =
                                   let uu____3900 =
                                     FStar_Syntax_Subst.compress lift_ty  in
                                   uu____3900.FStar_Syntax_Syntax.n  in
                                 match uu____3899 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____3912) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (3))
                                     ->
                                     let uu____3940 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____3940 with
                                      | (a'1,uu____3950)::(wp',uu____3952)::bs1
                                          ->
                                          let uu____3982 =
                                            FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 Prims.int_one) bs1
                                             in
                                          (match uu____3982 with
                                           | (bs2,uu____4025) ->
                                               let substs =
                                                 let uu____4061 =
                                                   let uu____4062 =
                                                     let uu____4069 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a)
                                                        in
                                                     (a'1, uu____4069)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____4062
                                                    in
                                                 let uu____4076 =
                                                   let uu____4079 =
                                                     let uu____4080 =
                                                       let uu____4087 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              wp)
                                                          in
                                                       (wp', uu____4087)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4080
                                                      in
                                                   [uu____4079]  in
                                                 uu____4061 :: uu____4076  in
                                               FStar_Syntax_Subst.subst_binders
                                                 substs bs2)
                                      | uu____4094 -> failwith "Impossible!")
                                 | uu____4104 ->
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_UnexpectedEffect,
                                         "") r
                                  in
                               let f =
                                 let f_sort =
                                   let uu____4125 =
                                     let uu____4134 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_Syntax_Syntax.t_unit
                                        in
                                     [uu____4134]  in
                                   let uu____4153 =
                                     let uu____4156 =
                                       let uu____4157 =
                                         let uu____4160 =
                                           FStar_All.pipe_right a
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_All.pipe_right uu____4160
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       let uu____4171 =
                                         let uu____4182 =
                                           let uu____4191 =
                                             let uu____4192 =
                                               FStar_All.pipe_right wp
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____4192
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           FStar_All.pipe_right uu____4191
                                             FStar_Syntax_Syntax.as_arg
                                            in
                                         [uu____4182]  in
                                       {
                                         FStar_Syntax_Syntax.comp_univs =
                                           [u_a];
                                         FStar_Syntax_Syntax.effect_name =
                                           (sub1.FStar_Syntax_Syntax.source);
                                         FStar_Syntax_Syntax.result_typ =
                                           uu____4157;
                                         FStar_Syntax_Syntax.effect_args =
                                           uu____4171;
                                         FStar_Syntax_Syntax.flags = []
                                       }  in
                                     FStar_Syntax_Syntax.mk_Comp uu____4156
                                      in
                                   FStar_Syntax_Util.arrow uu____4125
                                     uu____4153
                                    in
                                 let uu____4225 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None f_sort
                                    in
                                 FStar_All.pipe_right uu____4225
                                   FStar_Syntax_Syntax.mk_binder
                                  in
                               let bs = a :: wp ::
                                 (FStar_List.append rest_bs [f])  in
                               let uu____4272 =
                                 let uu____4277 =
                                   FStar_TypeChecker_Env.push_binders env0 bs
                                    in
                                 let uu____4278 =
                                   let uu____4279 =
                                     FStar_All.pipe_right a
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____4279
                                     FStar_Syntax_Syntax.bv_to_name
                                    in
                                 FStar_TypeChecker_Util.fresh_layered_effect_repr_en
                                   uu____4277 r
                                   sub1.FStar_Syntax_Syntax.target u_a
                                   uu____4278
                                  in
                               (match uu____4272 with
                                | (repr,g_repr) ->
                                    let uu____4296 =
                                      let uu____4299 =
                                        let uu____4302 =
                                          let uu____4305 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_All.pipe_right uu____4305
                                            (fun _4308  ->
                                               FStar_Pervasives_Native.Some
                                                 _4308)
                                           in
                                        FStar_Syntax_Syntax.mk_Total' repr
                                          uu____4302
                                         in
                                      FStar_Syntax_Util.arrow bs uu____4299
                                       in
                                    (uu____4296, g_repr)))
                       in
                    match uu____3776 with
                    | (k,g_k) ->
                        ((let uu____4318 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____4318
                          then
                            let uu____4323 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print1 "Before unification k: %s\n"
                              uu____4323
                          else ());
                         (let g1 = FStar_TypeChecker_Rel.teq env0 lift_ty k
                             in
                          FStar_TypeChecker_Rel.force_trivial_guard env0 g_k;
                          FStar_TypeChecker_Rel.force_trivial_guard env0 g1;
                          (let uu____4332 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffects")
                              in
                           if uu____4332
                           then
                             let uu____4337 =
                               FStar_Syntax_Print.term_to_string k  in
                             FStar_Util.print1 "After unification k: %s\n"
                               uu____4337
                           else ());
                          (let uu____4342 =
                             FStar_TypeChecker_Util.generalize_universes env0
                               lift1
                              in
                           match uu____4342 with
                           | (us1,lift2) ->
                               let lift_wp =
                                 let uu____4356 =
                                   let uu____4357 =
                                     let uu____4362 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env0 us1
                                        in
                                     FStar_TypeChecker_Normalize.remove_uvar_solutions
                                       uu____4362
                                      in
                                   FStar_All.pipe_right k uu____4357  in
                                 FStar_All.pipe_right uu____4356
                                   (FStar_Syntax_Subst.close_univ_vars us1)
                                  in
                               let sub2 =
                                 let uu___548_4366 = sub1  in
                                 {
                                   FStar_Syntax_Syntax.source =
                                     (uu___548_4366.FStar_Syntax_Syntax.source);
                                   FStar_Syntax_Syntax.target =
                                     (uu___548_4366.FStar_Syntax_Syntax.target);
                                   FStar_Syntax_Syntax.lift_wp =
                                     (FStar_Pervasives_Native.Some
                                        (us1, lift_wp));
                                   FStar_Syntax_Syntax.lift =
                                     (FStar_Pervasives_Native.Some
                                        (us1, lift2))
                                 }  in
                               ((let uu____4376 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env0)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____4376
                                 then
                                   let uu____4381 =
                                     FStar_Syntax_Print.sub_eff_to_string
                                       sub2
                                      in
                                   FStar_Util.print1 "Final sub_effect: %s\n"
                                     uu____4381
                                 else ());
                                sub2))))))))))
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      (let uu____4398 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "ED")
          in
       if uu____4398
       then
         let uu____4403 = FStar_Syntax_Print.eff_decl_to_string false ed  in
         FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____4403
       else ());
      (let uu____4409 =
         let uu____4414 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____4414 with
         | (ed_univs_subst,ed_univs) ->
             let bs =
               let uu____4438 =
                 FStar_Syntax_Subst.subst_binders ed_univs_subst
                   ed.FStar_Syntax_Syntax.binders
                  in
               FStar_Syntax_Subst.open_binders uu____4438  in
             let uu____4439 =
               let uu____4446 =
                 FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
               FStar_TypeChecker_TcTerm.tc_tparams uu____4446 bs  in
             (match uu____4439 with
              | (bs1,uu____4452,uu____4453) ->
                  let uu____4454 =
                    let tmp_t =
                      let uu____4464 =
                        let uu____4467 =
                          FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                            (fun _4472  -> FStar_Pervasives_Native.Some _4472)
                           in
                        FStar_Syntax_Syntax.mk_Total'
                          FStar_Syntax_Syntax.t_unit uu____4467
                         in
                      FStar_Syntax_Util.arrow bs1 uu____4464  in
                    let uu____4473 =
                      FStar_TypeChecker_Util.generalize_universes env0 tmp_t
                       in
                    match uu____4473 with
                    | (us,tmp_t1) ->
                        let uu____4490 =
                          let uu____4491 =
                            let uu____4492 =
                              FStar_All.pipe_right tmp_t1
                                FStar_Syntax_Util.arrow_formals
                               in
                            FStar_All.pipe_right uu____4492
                              FStar_Pervasives_Native.fst
                             in
                          FStar_All.pipe_right uu____4491
                            FStar_Syntax_Subst.close_binders
                           in
                        (us, uu____4490)
                     in
                  (match uu____4454 with
                   | (us,bs2) ->
                       (match ed_univs with
                        | [] -> (us, bs2)
                        | uu____4561 ->
                            let uu____4564 =
                              ((FStar_List.length ed_univs) =
                                 (FStar_List.length us))
                                &&
                                (FStar_List.forall2
                                   (fun u1  ->
                                      fun u2  ->
                                        let uu____4571 =
                                          FStar_Syntax_Syntax.order_univ_name
                                            u1 u2
                                           in
                                        uu____4571 = Prims.int_zero) ed_univs
                                   us)
                               in
                            if uu____4564
                            then (us, bs2)
                            else
                              (let uu____4582 =
                                 let uu____4588 =
                                   let uu____4590 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length ed_univs)
                                      in
                                   let uu____4592 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length us)
                                      in
                                   FStar_Util.format3
                                     "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                     uu____4590 uu____4592
                                    in
                                 (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                   uu____4588)
                                  in
                               let uu____4596 =
                                 FStar_Ident.range_of_lid
                                   ed.FStar_Syntax_Syntax.mname
                                  in
                               FStar_Errors.raise_error uu____4582 uu____4596))))
          in
       match uu____4409 with
       | (us,bs) ->
           let ed1 =
             let uu___580_4604 = ed  in
             {
               FStar_Syntax_Syntax.is_layered =
                 (uu___580_4604.FStar_Syntax_Syntax.is_layered);
               FStar_Syntax_Syntax.cattributes =
                 (uu___580_4604.FStar_Syntax_Syntax.cattributes);
               FStar_Syntax_Syntax.mname =
                 (uu___580_4604.FStar_Syntax_Syntax.mname);
               FStar_Syntax_Syntax.univs = us;
               FStar_Syntax_Syntax.binders = bs;
               FStar_Syntax_Syntax.signature =
                 (uu___580_4604.FStar_Syntax_Syntax.signature);
               FStar_Syntax_Syntax.ret_wp =
                 (uu___580_4604.FStar_Syntax_Syntax.ret_wp);
               FStar_Syntax_Syntax.bind_wp =
                 (uu___580_4604.FStar_Syntax_Syntax.bind_wp);
               FStar_Syntax_Syntax.stronger =
                 (uu___580_4604.FStar_Syntax_Syntax.stronger);
               FStar_Syntax_Syntax.match_wps =
                 (uu___580_4604.FStar_Syntax_Syntax.match_wps);
               FStar_Syntax_Syntax.trivial =
                 (uu___580_4604.FStar_Syntax_Syntax.trivial);
               FStar_Syntax_Syntax.repr =
                 (uu___580_4604.FStar_Syntax_Syntax.repr);
               FStar_Syntax_Syntax.return_repr =
                 (uu___580_4604.FStar_Syntax_Syntax.return_repr);
               FStar_Syntax_Syntax.bind_repr =
                 (uu___580_4604.FStar_Syntax_Syntax.bind_repr);
               FStar_Syntax_Syntax.stronger_repr =
                 (uu___580_4604.FStar_Syntax_Syntax.stronger_repr);
               FStar_Syntax_Syntax.actions =
                 (uu___580_4604.FStar_Syntax_Syntax.actions);
               FStar_Syntax_Syntax.eff_attrs =
                 (uu___580_4604.FStar_Syntax_Syntax.eff_attrs)
             }  in
           let uu____4605 = FStar_Syntax_Subst.univ_var_opening us  in
           (match uu____4605 with
            | (ed_univs_subst,ed_univs) ->
                let uu____4624 =
                  let uu____4629 =
                    FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                  FStar_Syntax_Subst.open_binders' uu____4629  in
                (match uu____4624 with
                 | (ed_bs,ed_bs_subst) ->
                     let ed2 =
                       let op uu____4650 =
                         match uu____4650 with
                         | (us1,t) ->
                             let t1 =
                               let uu____4670 =
                                 FStar_Syntax_Subst.shift_subst
                                   ((FStar_List.length ed_bs) +
                                      (FStar_List.length us1)) ed_univs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____4670 t  in
                             let uu____4679 =
                               let uu____4680 =
                                 FStar_Syntax_Subst.shift_subst
                                   (FStar_List.length us1) ed_bs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____4680 t1  in
                             (us1, uu____4679)
                          in
                       let uu___594_4685 = ed1  in
                       let uu____4686 = op ed1.FStar_Syntax_Syntax.signature
                          in
                       let uu____4687 = op ed1.FStar_Syntax_Syntax.ret_wp  in
                       let uu____4688 = op ed1.FStar_Syntax_Syntax.bind_wp
                          in
                       let uu____4689 = op ed1.FStar_Syntax_Syntax.stronger
                          in
                       let uu____4690 =
                         FStar_Syntax_Util.map_match_wps op
                           ed1.FStar_Syntax_Syntax.match_wps
                          in
                       let uu____4695 =
                         FStar_Util.map_opt ed1.FStar_Syntax_Syntax.trivial
                           op
                          in
                       let uu____4698 = op ed1.FStar_Syntax_Syntax.repr  in
                       let uu____4699 =
                         op ed1.FStar_Syntax_Syntax.return_repr  in
                       let uu____4700 = op ed1.FStar_Syntax_Syntax.bind_repr
                          in
                       let uu____4701 =
                         FStar_List.map
                           (fun a  ->
                              let uu___597_4709 = a  in
                              let uu____4710 =
                                let uu____4711 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_defn))
                                   in
                                FStar_Pervasives_Native.snd uu____4711  in
                              let uu____4722 =
                                let uu____4723 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_typ))
                                   in
                                FStar_Pervasives_Native.snd uu____4723  in
                              {
                                FStar_Syntax_Syntax.action_name =
                                  (uu___597_4709.FStar_Syntax_Syntax.action_name);
                                FStar_Syntax_Syntax.action_unqualified_name =
                                  (uu___597_4709.FStar_Syntax_Syntax.action_unqualified_name);
                                FStar_Syntax_Syntax.action_univs =
                                  (uu___597_4709.FStar_Syntax_Syntax.action_univs);
                                FStar_Syntax_Syntax.action_params =
                                  (uu___597_4709.FStar_Syntax_Syntax.action_params);
                                FStar_Syntax_Syntax.action_defn = uu____4710;
                                FStar_Syntax_Syntax.action_typ = uu____4722
                              }) ed1.FStar_Syntax_Syntax.actions
                          in
                       {
                         FStar_Syntax_Syntax.is_layered =
                           (uu___594_4685.FStar_Syntax_Syntax.is_layered);
                         FStar_Syntax_Syntax.cattributes =
                           (uu___594_4685.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.mname =
                           (uu___594_4685.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.univs =
                           (uu___594_4685.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___594_4685.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature = uu____4686;
                         FStar_Syntax_Syntax.ret_wp = uu____4687;
                         FStar_Syntax_Syntax.bind_wp = uu____4688;
                         FStar_Syntax_Syntax.stronger = uu____4689;
                         FStar_Syntax_Syntax.match_wps = uu____4690;
                         FStar_Syntax_Syntax.trivial = uu____4695;
                         FStar_Syntax_Syntax.repr = uu____4698;
                         FStar_Syntax_Syntax.return_repr = uu____4699;
                         FStar_Syntax_Syntax.bind_repr = uu____4700;
                         FStar_Syntax_Syntax.stronger_repr =
                           FStar_Pervasives_Native.None;
                         FStar_Syntax_Syntax.actions = uu____4701;
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___594_4685.FStar_Syntax_Syntax.eff_attrs)
                       }  in
                     ((let uu____4735 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env0)
                           (FStar_Options.Other "ED")
                          in
                       if uu____4735
                       then
                         let uu____4740 =
                           FStar_Syntax_Print.eff_decl_to_string false ed2
                            in
                         FStar_Util.print1
                           "After typechecking binders eff_decl: \n\t%s\n"
                           uu____4740
                       else ());
                      (let env =
                         let uu____4747 =
                           FStar_TypeChecker_Env.push_univ_vars env0 ed_univs
                            in
                         FStar_TypeChecker_Env.push_binders uu____4747 ed_bs
                          in
                       let check_and_gen' comb n1 env_opt uu____4782 k =
                         match uu____4782 with
                         | (us1,t) ->
                             let env1 =
                               if FStar_Util.is_some env_opt
                               then
                                 FStar_All.pipe_right env_opt FStar_Util.must
                               else env  in
                             let uu____4802 =
                               FStar_Syntax_Subst.open_univ_vars us1 t  in
                             (match uu____4802 with
                              | (us2,t1) ->
                                  let t2 =
                                    match k with
                                    | FStar_Pervasives_Native.Some k1 ->
                                        let uu____4811 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env1 us2
                                           in
                                        tc_check_trivial_guard uu____4811 t1
                                          k1
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____4812 =
                                          let uu____4819 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            uu____4819 t1
                                           in
                                        (match uu____4812 with
                                         | (t2,uu____4821,g) ->
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env1 g;
                                              t2))
                                     in
                                  let uu____4824 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env1 t2
                                     in
                                  (match uu____4824 with
                                   | (g_us,t3) ->
                                       (if (FStar_List.length g_us) <> n1
                                        then
                                          (let error =
                                             let uu____4840 =
                                               FStar_Util.string_of_int n1
                                                in
                                             let uu____4842 =
                                               let uu____4844 =
                                                 FStar_All.pipe_right g_us
                                                   FStar_List.length
                                                  in
                                               FStar_All.pipe_right
                                                 uu____4844
                                                 FStar_Util.string_of_int
                                                in
                                             FStar_Util.format4
                                               "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                               (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                               comb uu____4840 uu____4842
                                              in
                                           FStar_Errors.raise_error
                                             (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                               error)
                                             t3.FStar_Syntax_Syntax.pos)
                                        else ();
                                        (match us2 with
                                         | [] -> (g_us, t3)
                                         | uu____4859 ->
                                             let uu____4860 =
                                               ((FStar_List.length us2) =
                                                  (FStar_List.length g_us))
                                                 &&
                                                 (FStar_List.forall2
                                                    (fun u1  ->
                                                       fun u2  ->
                                                         let uu____4867 =
                                                           FStar_Syntax_Syntax.order_univ_name
                                                             u1 u2
                                                            in
                                                         uu____4867 =
                                                           Prims.int_zero)
                                                    us2 g_us)
                                                in
                                             if uu____4860
                                             then (g_us, t3)
                                             else
                                               (let uu____4878 =
                                                  let uu____4884 =
                                                    let uu____4886 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           us2)
                                                       in
                                                    let uu____4888 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           g_us)
                                                       in
                                                    FStar_Util.format4
                                                      "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                      (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      comb uu____4886
                                                      uu____4888
                                                     in
                                                  (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                    uu____4884)
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4878
                                                  t3.FStar_Syntax_Syntax.pos)))))
                          in
                       let signature =
                         check_and_gen' "signature" Prims.int_one
                           FStar_Pervasives_Native.None
                           ed2.FStar_Syntax_Syntax.signature
                           FStar_Pervasives_Native.None
                          in
                       (let uu____4896 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env0)
                            (FStar_Options.Other "ED")
                           in
                        if uu____4896
                        then
                          let uu____4901 =
                            FStar_Syntax_Print.tscheme_to_string signature
                             in
                          FStar_Util.print1 "Typechecked signature: %s\n"
                            uu____4901
                        else ());
                       (let fresh_a_and_wp uu____4917 =
                          let fail1 t =
                            let uu____4930 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env ed2.FStar_Syntax_Syntax.mname t
                               in
                            FStar_Errors.raise_error uu____4930
                              (FStar_Pervasives_Native.snd
                                 ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                             in
                          let uu____4946 =
                            FStar_TypeChecker_Env.inst_tscheme signature  in
                          match uu____4946 with
                          | (uu____4957,signature1) ->
                              let uu____4959 =
                                let uu____4960 =
                                  FStar_Syntax_Subst.compress signature1  in
                                uu____4960.FStar_Syntax_Syntax.n  in
                              (match uu____4959 with
                               | FStar_Syntax_Syntax.Tm_arrow
                                   (bs1,uu____4970) ->
                                   let bs2 =
                                     FStar_Syntax_Subst.open_binders bs1  in
                                   (match bs2 with
                                    | (a,uu____4999)::(wp,uu____5001)::[] ->
                                        (a, (wp.FStar_Syntax_Syntax.sort))
                                    | uu____5030 -> fail1 signature1)
                               | uu____5031 -> fail1 signature1)
                           in
                        let log_combinator s ts =
                          let uu____5045 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5045
                          then
                            let uu____5050 =
                              FStar_Syntax_Print.tscheme_to_string ts  in
                            FStar_Util.print3 "Typechecked %s:%s = %s\n"
                              (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                              s uu____5050
                          else ()  in
                        let ret_wp =
                          let uu____5056 = fresh_a_and_wp ()  in
                          match uu____5056 with
                          | (a,wp_sort) ->
                              let k =
                                let uu____5072 =
                                  let uu____5081 =
                                    FStar_Syntax_Syntax.mk_binder a  in
                                  let uu____5088 =
                                    let uu____5097 =
                                      let uu____5104 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      FStar_Syntax_Syntax.null_binder
                                        uu____5104
                                       in
                                    [uu____5097]  in
                                  uu____5081 :: uu____5088  in
                                let uu____5123 =
                                  FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                FStar_Syntax_Util.arrow uu____5072 uu____5123
                                 in
                              check_and_gen' "ret_wp" Prims.int_one
                                FStar_Pervasives_Native.None
                                ed2.FStar_Syntax_Syntax.ret_wp
                                (FStar_Pervasives_Native.Some k)
                           in
                        log_combinator "ret_wp" ret_wp;
                        (let bind_wp =
                           let uu____5131 = fresh_a_and_wp ()  in
                           match uu____5131 with
                           | (a,wp_sort_a) ->
                               let uu____5144 = fresh_a_and_wp ()  in
                               (match uu____5144 with
                                | (b,wp_sort_b) ->
                                    let wp_sort_a_b =
                                      let uu____5160 =
                                        let uu____5169 =
                                          let uu____5176 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____5176
                                           in
                                        [uu____5169]  in
                                      let uu____5189 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____5160
                                        uu____5189
                                       in
                                    let k =
                                      let uu____5195 =
                                        let uu____5204 =
                                          FStar_Syntax_Syntax.null_binder
                                            FStar_Syntax_Syntax.t_range
                                           in
                                        let uu____5211 =
                                          let uu____5220 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____5227 =
                                            let uu____5236 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____5243 =
                                              let uu____5252 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              let uu____5259 =
                                                let uu____5268 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a_b
                                                   in
                                                [uu____5268]  in
                                              uu____5252 :: uu____5259  in
                                            uu____5236 :: uu____5243  in
                                          uu____5220 :: uu____5227  in
                                        uu____5204 :: uu____5211  in
                                      let uu____5311 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____5195
                                        uu____5311
                                       in
                                    check_and_gen' "bind_wp"
                                      (Prims.of_int (2))
                                      FStar_Pervasives_Native.None
                                      ed2.FStar_Syntax_Syntax.bind_wp
                                      (FStar_Pervasives_Native.Some k))
                            in
                         log_combinator "bind_wp" bind_wp;
                         (let stronger =
                            let uu____5319 = fresh_a_and_wp ()  in
                            match uu____5319 with
                            | (a,wp_sort_a) ->
                                let uu____5332 = FStar_Syntax_Util.type_u ()
                                   in
                                (match uu____5332 with
                                 | (t,uu____5338) ->
                                     let k =
                                       let uu____5342 =
                                         let uu____5351 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____5358 =
                                           let uu____5367 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____5374 =
                                             let uu____5383 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____5383]  in
                                           uu____5367 :: uu____5374  in
                                         uu____5351 :: uu____5358  in
                                       let uu____5414 =
                                         FStar_Syntax_Syntax.mk_Total t  in
                                       FStar_Syntax_Util.arrow uu____5342
                                         uu____5414
                                        in
                                     check_and_gen' "stronger" Prims.int_one
                                       FStar_Pervasives_Native.None
                                       ed2.FStar_Syntax_Syntax.stronger
                                       (FStar_Pervasives_Native.Some k))
                             in
                          log_combinator "stronger" stronger;
                          (let match_wps =
                             let uu____5426 =
                               FStar_Syntax_Util.get_match_with_close_wps
                                 ed2.FStar_Syntax_Syntax.match_wps
                                in
                             match uu____5426 with
                             | (if_then_else1,ite_wp,close_wp) ->
                                 let if_then_else2 =
                                   let uu____5441 = fresh_a_and_wp ()  in
                                   match uu____5441 with
                                   | (a,wp_sort_a) ->
                                       let p =
                                         let uu____5455 =
                                           let uu____5458 =
                                             FStar_Ident.range_of_lid
                                               ed2.FStar_Syntax_Syntax.mname
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____5458
                                            in
                                         let uu____5459 =
                                           let uu____5460 =
                                             FStar_Syntax_Util.type_u ()  in
                                           FStar_All.pipe_right uu____5460
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____5455 uu____5459
                                          in
                                       let k =
                                         let uu____5472 =
                                           let uu____5481 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____5488 =
                                             let uu____5497 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 p
                                                in
                                             let uu____5504 =
                                               let uu____5513 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               let uu____5520 =
                                                 let uu____5529 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____5529]  in
                                               uu____5513 :: uu____5520  in
                                             uu____5497 :: uu____5504  in
                                           uu____5481 :: uu____5488  in
                                         let uu____5566 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a
                                            in
                                         FStar_Syntax_Util.arrow uu____5472
                                           uu____5566
                                          in
                                       check_and_gen' "if_then_else"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         if_then_else1
                                         (FStar_Pervasives_Native.Some k)
                                    in
                                 (log_combinator "if_then_else" if_then_else2;
                                  (let ite_wp1 =
                                     let uu____5574 = fresh_a_and_wp ()  in
                                     match uu____5574 with
                                     | (a,wp_sort_a) ->
                                         let k =
                                           let uu____5590 =
                                             let uu____5599 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____5606 =
                                               let uu____5615 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____5615]  in
                                             uu____5599 :: uu____5606  in
                                           let uu____5640 =
                                             FStar_Syntax_Syntax.mk_Total
                                               wp_sort_a
                                              in
                                           FStar_Syntax_Util.arrow uu____5590
                                             uu____5640
                                            in
                                         check_and_gen' "ite_wp"
                                           Prims.int_one
                                           FStar_Pervasives_Native.None
                                           ite_wp
                                           (FStar_Pervasives_Native.Some k)
                                      in
                                   log_combinator "ite_wp" ite_wp1;
                                   (let close_wp1 =
                                      let uu____5648 = fresh_a_and_wp ()  in
                                      match uu____5648 with
                                      | (a,wp_sort_a) ->
                                          let b =
                                            let uu____5662 =
                                              let uu____5665 =
                                                FStar_Ident.range_of_lid
                                                  ed2.FStar_Syntax_Syntax.mname
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____5665
                                               in
                                            let uu____5666 =
                                              let uu____5667 =
                                                FStar_Syntax_Util.type_u ()
                                                 in
                                              FStar_All.pipe_right uu____5667
                                                FStar_Pervasives_Native.fst
                                               in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____5662 uu____5666
                                             in
                                          let wp_sort_b_a =
                                            let uu____5679 =
                                              let uu____5688 =
                                                let uu____5695 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    b
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____5695
                                                 in
                                              [uu____5688]  in
                                            let uu____5708 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____5679 uu____5708
                                             in
                                          let k =
                                            let uu____5714 =
                                              let uu____5723 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____5730 =
                                                let uu____5739 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    b
                                                   in
                                                let uu____5746 =
                                                  let uu____5755 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_b_a
                                                     in
                                                  [uu____5755]  in
                                                uu____5739 :: uu____5746  in
                                              uu____5723 :: uu____5730  in
                                            let uu____5786 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____5714 uu____5786
                                             in
                                          check_and_gen' "close_wp"
                                            (Prims.of_int (2))
                                            FStar_Pervasives_Native.None
                                            close_wp
                                            (FStar_Pervasives_Native.Some k)
                                       in
                                    log_combinator "close_wp" close_wp1;
                                    FStar_Util.Inl
                                      {
                                        FStar_Syntax_Syntax.if_then_else =
                                          if_then_else2;
                                        FStar_Syntax_Syntax.ite_wp = ite_wp1;
                                        FStar_Syntax_Syntax.close_wp =
                                          close_wp1
                                      })))
                              in
                           let trivial =
                             let uu____5796 = fresh_a_and_wp ()  in
                             match uu____5796 with
                             | (a,wp_sort_a) ->
                                 let uu____5811 = FStar_Syntax_Util.type_u ()
                                    in
                                 (match uu____5811 with
                                  | (t,uu____5819) ->
                                      let k =
                                        let uu____5823 =
                                          let uu____5832 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____5839 =
                                            let uu____5848 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_sort_a
                                               in
                                            [uu____5848]  in
                                          uu____5832 :: uu____5839  in
                                        let uu____5873 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____5823
                                          uu____5873
                                         in
                                      let trivial =
                                        let uu____5877 =
                                          FStar_All.pipe_right
                                            ed2.FStar_Syntax_Syntax.trivial
                                            FStar_Util.must
                                           in
                                        check_and_gen' "trivial"
                                          Prims.int_one
                                          FStar_Pervasives_Native.None
                                          uu____5877
                                          (FStar_Pervasives_Native.Some k)
                                         in
                                      (log_combinator "trivial" trivial;
                                       FStar_Pervasives_Native.Some trivial))
                              in
                           let uu____5892 =
                             let uu____5903 =
                               let uu____5904 =
                                 FStar_Syntax_Subst.compress
                                   (FStar_Pervasives_Native.snd
                                      ed2.FStar_Syntax_Syntax.repr)
                                  in
                               uu____5904.FStar_Syntax_Syntax.n  in
                             match uu____5903 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____5923 ->
                                 let repr =
                                   let uu____5925 = fresh_a_and_wp ()  in
                                   match uu____5925 with
                                   | (a,wp_sort_a) ->
                                       let uu____5938 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____5938 with
                                        | (t,uu____5944) ->
                                            let k =
                                              let uu____5948 =
                                                let uu____5957 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____5964 =
                                                  let uu____5973 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a
                                                     in
                                                  [uu____5973]  in
                                                uu____5957 :: uu____5964  in
                                              let uu____5998 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____5948 uu____5998
                                               in
                                            check_and_gen' "repr"
                                              Prims.int_one
                                              FStar_Pervasives_Native.None
                                              ed2.FStar_Syntax_Syntax.repr
                                              (FStar_Pervasives_Native.Some k))
                                    in
                                 (log_combinator "repr" repr;
                                  (let mk_repr' t wp =
                                     let uu____6018 =
                                       FStar_TypeChecker_Env.inst_tscheme
                                         repr
                                        in
                                     match uu____6018 with
                                     | (uu____6025,repr1) ->
                                         let repr2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.EraseUniverses;
                                             FStar_TypeChecker_Env.AllowUnboundUniverses]
                                             env repr1
                                            in
                                         let uu____6028 =
                                           let uu____6035 =
                                             let uu____6036 =
                                               let uu____6053 =
                                                 let uu____6064 =
                                                   FStar_All.pipe_right t
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____6081 =
                                                   let uu____6092 =
                                                     FStar_All.pipe_right wp
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____6092]  in
                                                 uu____6064 :: uu____6081  in
                                               (repr2, uu____6053)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____6036
                                              in
                                           FStar_Syntax_Syntax.mk uu____6035
                                            in
                                         uu____6028
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                      in
                                   let mk_repr a wp =
                                     let uu____6158 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     mk_repr' uu____6158 wp  in
                                   let destruct_repr t =
                                     let uu____6173 =
                                       let uu____6174 =
                                         FStar_Syntax_Subst.compress t  in
                                       uu____6174.FStar_Syntax_Syntax.n  in
                                     match uu____6173 with
                                     | FStar_Syntax_Syntax.Tm_app
                                         (uu____6185,(t1,uu____6187)::
                                          (wp,uu____6189)::[])
                                         -> (t1, wp)
                                     | uu____6248 ->
                                         failwith "Unexpected repr type"
                                      in
                                   let return_repr =
                                     let uu____6259 = fresh_a_and_wp ()  in
                                     match uu____6259 with
                                     | (a,uu____6267) ->
                                         let x_a =
                                           let uu____6273 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x_a"
                                             FStar_Pervasives_Native.None
                                             uu____6273
                                            in
                                         let res =
                                           let wp =
                                             let uu____6281 =
                                               let uu____6286 =
                                                 let uu____6287 =
                                                   FStar_TypeChecker_Env.inst_tscheme
                                                     ret_wp
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____6287
                                                   FStar_Pervasives_Native.snd
                                                  in
                                               let uu____6296 =
                                                 let uu____6297 =
                                                   let uu____6306 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6306
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____6315 =
                                                   let uu____6326 =
                                                     let uu____6335 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         x_a
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____6335
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____6326]  in
                                                 uu____6297 :: uu____6315  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____6286 uu____6296
                                                in
                                             uu____6281
                                               FStar_Pervasives_Native.None
                                               FStar_Range.dummyRange
                                              in
                                           mk_repr a wp  in
                                         let k =
                                           let uu____6371 =
                                             let uu____6380 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____6387 =
                                               let uu____6396 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   x_a
                                                  in
                                               [uu____6396]  in
                                             uu____6380 :: uu____6387  in
                                           let uu____6421 =
                                             FStar_Syntax_Syntax.mk_Total res
                                              in
                                           FStar_Syntax_Util.arrow uu____6371
                                             uu____6421
                                            in
                                         let uu____6424 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env k
                                            in
                                         (match uu____6424 with
                                          | (k1,uu____6432,uu____6433) ->
                                              let env1 =
                                                let uu____6437 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env
                                                    (FStar_Pervasives_Native.snd
                                                       ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____6437
                                                 in
                                              check_and_gen' "return_repr"
                                                Prims.int_one env1
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                (FStar_Pervasives_Native.Some
                                                   k1))
                                      in
                                   log_combinator "return_repr" return_repr;
                                   (let bind_repr =
                                      let r =
                                        let uu____6448 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            FStar_Parser_Const.range_0
                                            FStar_Syntax_Syntax.delta_constant
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_All.pipe_right uu____6448
                                          FStar_Syntax_Syntax.fv_to_tm
                                         in
                                      let uu____6449 = fresh_a_and_wp ()  in
                                      match uu____6449 with
                                      | (a,wp_sort_a) ->
                                          let uu____6462 = fresh_a_and_wp ()
                                             in
                                          (match uu____6462 with
                                           | (b,wp_sort_b) ->
                                               let wp_sort_a_b =
                                                 let uu____6478 =
                                                   let uu____6487 =
                                                     let uu____6494 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____6494
                                                      in
                                                   [uu____6487]  in
                                                 let uu____6507 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     wp_sort_b
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____6478 uu____6507
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
                                                 let uu____6515 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     a
                                                    in
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "x_a"
                                                   FStar_Pervasives_Native.None
                                                   uu____6515
                                                  in
                                               let wp_g_x =
                                                 let uu____6520 =
                                                   let uu____6525 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       wp_g
                                                      in
                                                   let uu____6526 =
                                                     let uu____6527 =
                                                       let uu____6536 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x_a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____6536
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____6527]  in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     uu____6525 uu____6526
                                                    in
                                                 uu____6520
                                                   FStar_Pervasives_Native.None
                                                   FStar_Range.dummyRange
                                                  in
                                               let res =
                                                 let wp =
                                                   let uu____6567 =
                                                     let uu____6572 =
                                                       let uu____6573 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           bind_wp
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____6573
                                                         FStar_Pervasives_Native.snd
                                                        in
                                                     let uu____6582 =
                                                       let uu____6583 =
                                                         let uu____6586 =
                                                           let uu____6589 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               a
                                                              in
                                                           let uu____6590 =
                                                             let uu____6593 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 b
                                                                in
                                                             let uu____6594 =
                                                               let uu____6597
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_f
                                                                  in
                                                               let uu____6598
                                                                 =
                                                                 let uu____6601
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g
                                                                    in
                                                                 [uu____6601]
                                                                  in
                                                               uu____6597 ::
                                                                 uu____6598
                                                                in
                                                             uu____6593 ::
                                                               uu____6594
                                                              in
                                                           uu____6589 ::
                                                             uu____6590
                                                            in
                                                         r :: uu____6586  in
                                                       FStar_List.map
                                                         FStar_Syntax_Syntax.as_arg
                                                         uu____6583
                                                        in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____6572 uu____6582
                                                      in
                                                   uu____6567
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 mk_repr b wp  in
                                               let maybe_range_arg =
                                                 let uu____6619 =
                                                   FStar_Util.for_some
                                                     (FStar_Syntax_Util.attr_eq
                                                        FStar_Syntax_Util.dm4f_bind_range_attr)
                                                     ed2.FStar_Syntax_Syntax.eff_attrs
                                                    in
                                                 if uu____6619
                                                 then
                                                   let uu____6630 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       FStar_Syntax_Syntax.t_range
                                                      in
                                                   let uu____6637 =
                                                     let uu____6646 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         FStar_Syntax_Syntax.t_range
                                                        in
                                                     [uu____6646]  in
                                                   uu____6630 :: uu____6637
                                                 else []  in
                                               let k =
                                                 let uu____6682 =
                                                   let uu____6691 =
                                                     let uu____6700 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6707 =
                                                       let uu____6716 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           b
                                                          in
                                                       [uu____6716]  in
                                                     uu____6700 :: uu____6707
                                                      in
                                                   let uu____6741 =
                                                     let uu____6750 =
                                                       let uu____6759 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           wp_f
                                                          in
                                                       let uu____6766 =
                                                         let uu____6775 =
                                                           let uu____6782 =
                                                             let uu____6783 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp_f
                                                                in
                                                             mk_repr a
                                                               uu____6783
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____6782
                                                            in
                                                         let uu____6784 =
                                                           let uu____6793 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               wp_g
                                                              in
                                                           let uu____6800 =
                                                             let uu____6809 =
                                                               let uu____6816
                                                                 =
                                                                 let uu____6817
                                                                   =
                                                                   let uu____6826
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                   [uu____6826]
                                                                    in
                                                                 let uu____6845
                                                                   =
                                                                   let uu____6848
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                   FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____6848
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   uu____6817
                                                                   uu____6845
                                                                  in
                                                               FStar_Syntax_Syntax.null_binder
                                                                 uu____6816
                                                                in
                                                             [uu____6809]  in
                                                           uu____6793 ::
                                                             uu____6800
                                                            in
                                                         uu____6775 ::
                                                           uu____6784
                                                          in
                                                       uu____6759 ::
                                                         uu____6766
                                                        in
                                                     FStar_List.append
                                                       maybe_range_arg
                                                       uu____6750
                                                      in
                                                   FStar_List.append
                                                     uu____6691 uu____6741
                                                    in
                                                 let uu____6893 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     res
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____6682 uu____6893
                                                  in
                                               let uu____6896 =
                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                   env k
                                                  in
                                               (match uu____6896 with
                                                | (k1,uu____6904,uu____6905)
                                                    ->
                                                    let env1 =
                                                      FStar_TypeChecker_Env.set_range
                                                        env
                                                        (FStar_Pervasives_Native.snd
                                                           ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                       in
                                                    let env2 =
                                                      FStar_All.pipe_right
                                                        (let uu___795_6917 =
                                                           env1  in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.instantiate_imp);
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             = true;
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.try_solve_implicits_hook
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.nbe);
                                                           FStar_TypeChecker_Env.strict_args_tab
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.strict_args_tab)
                                                         })
                                                        (fun _6919  ->
                                                           FStar_Pervasives_Native.Some
                                                             _6919)
                                                       in
                                                    check_and_gen'
                                                      "bind_repr"
                                                      (Prims.of_int (2)) env2
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
                                         (let uu____6946 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env, act)
                                            else
                                              (let uu____6960 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____6960 with
                                               | (usubst,uvs) ->
                                                   let uu____6983 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env uvs
                                                      in
                                                   let uu____6984 =
                                                     let uu___808_6985 = act
                                                        in
                                                     let uu____6986 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____6987 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___808_6985.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___808_6985.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___808_6985.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____6986;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____6987
                                                     }  in
                                                   (uu____6983, uu____6984))
                                             in
                                          match uu____6946 with
                                          | (env1,act1) ->
                                              let act_typ =
                                                let uu____6991 =
                                                  let uu____6992 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  uu____6992.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____6991 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs1,c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c
                                                       in
                                                    let uu____7018 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname
                                                       in
                                                    if uu____7018
                                                    then
                                                      let uu____7021 =
                                                        let uu____7024 =
                                                          let uu____7025 =
                                                            let uu____7026 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____7026
                                                             in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____7025
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____7024
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____7021
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____7049 ->
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              let uu____7050 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env1 act_typ
                                                 in
                                              (match uu____7050 with
                                               | (act_typ1,uu____7058,g_t) ->
                                                   let env' =
                                                     let uu___825_7061 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env1 act_typ1
                                                        in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_sig
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.gamma_sig);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.attrtab
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.attrtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.phase1
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.phase1);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.uvar_subtyping
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.uvar_subtyping);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.fv_delta_depths
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.fv_delta_depths);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.try_solve_implicits_hook
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.postprocess
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.postprocess);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.nbe
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.nbe);
                                                       FStar_TypeChecker_Env.strict_args_tab
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.strict_args_tab)
                                                     }  in
                                                   ((let uu____7064 =
                                                       FStar_TypeChecker_Env.debug
                                                         env1
                                                         (FStar_Options.Other
                                                            "ED")
                                                        in
                                                     if uu____7064
                                                     then
                                                       let uu____7068 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name
                                                          in
                                                       let uu____7070 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____7072 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1
                                                          in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____7068
                                                         uu____7070
                                                         uu____7072
                                                     else ());
                                                    (let uu____7077 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     match uu____7077 with
                                                     | (act_defn,uu____7085,g_a)
                                                         ->
                                                         let act_defn1 =
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Env.UnfoldUntil
                                                                FStar_Syntax_Syntax.delta_constant]
                                                             env1 act_defn
                                                            in
                                                         let act_typ2 =
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Env.UnfoldUntil
                                                                FStar_Syntax_Syntax.delta_constant;
                                                             FStar_TypeChecker_Env.Eager_unfolding;
                                                             FStar_TypeChecker_Env.Beta]
                                                             env1 act_typ1
                                                            in
                                                         let uu____7089 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2
                                                              in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs1,c) ->
                                                               let uu____7125
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs1 c
                                                                  in
                                                               (match uu____7125
                                                                with
                                                                | (bs2,uu____7137)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____7144
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____7144
                                                                     in
                                                                    let uu____7147
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____7147
                                                                    with
                                                                    | 
                                                                    (k1,uu____7161,g)
                                                                    ->
                                                                    (k1, g)))
                                                           | uu____7165 ->
                                                               let uu____7166
                                                                 =
                                                                 let uu____7172
                                                                   =
                                                                   let uu____7174
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                   let uu____7176
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____7174
                                                                    uu____7176
                                                                    in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____7172)
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____7166
                                                                 act_defn1.FStar_Syntax_Syntax.pos
                                                            in
                                                         (match uu____7089
                                                          with
                                                          | (expected_k,g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env1
                                                                  act_typ2
                                                                  expected_k
                                                                 in
                                                              ((let uu____7194
                                                                  =
                                                                  let uu____7195
                                                                    =
                                                                    let uu____7196
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____7196
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____7195
                                                                   in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env1
                                                                  uu____7194);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____7198
                                                                    =
                                                                    let uu____7199
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____7199.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____7198
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____7224
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____7224
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____7231
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____7231
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____7251
                                                                    =
                                                                    let uu____7252
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____7252]
                                                                     in
                                                                    let uu____7253
                                                                    =
                                                                    let uu____7264
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____7264]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____7251;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____7253;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____7289
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____7289))
                                                                  | uu____7292
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                   in
                                                                let uu____7294
                                                                  =
                                                                  if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                  then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                  else
                                                                    (
                                                                    let uu____7316
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____7316))
                                                                   in
                                                                match uu____7294
                                                                with
                                                                | (univs1,act_defn2)
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
                                                                    let uu___875_7335
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___875_7335.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___875_7335.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___875_7335.FStar_Syntax_Syntax.action_params);
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
                                     (repr, return_repr, bind_repr, actions)))))
                              in
                           match uu____5892 with
                           | (repr,return_repr,bind_repr,actions) ->
                               let cl ts =
                                 let ts1 =
                                   FStar_Syntax_Subst.close_tscheme ed_bs ts
                                    in
                                 let ed_univs_closing =
                                   FStar_Syntax_Subst.univ_var_closing
                                     ed_univs
                                    in
                                 let uu____7360 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length ed_bs)
                                     ed_univs_closing
                                    in
                                 FStar_Syntax_Subst.subst_tscheme uu____7360
                                   ts1
                                  in
                               let ed3 =
                                 let uu___887_7370 = ed2  in
                                 let uu____7371 = cl signature  in
                                 let uu____7372 = cl ret_wp  in
                                 let uu____7373 = cl bind_wp  in
                                 let uu____7374 = cl stronger  in
                                 let uu____7375 =
                                   FStar_Syntax_Util.map_match_wps cl
                                     match_wps
                                    in
                                 let uu____7380 =
                                   FStar_Util.map_opt trivial cl  in
                                 let uu____7383 = cl repr  in
                                 let uu____7384 = cl return_repr  in
                                 let uu____7385 = cl bind_repr  in
                                 let uu____7386 =
                                   FStar_List.map
                                     (fun a  ->
                                        let uu___890_7394 = a  in
                                        let uu____7395 =
                                          let uu____7396 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_All.pipe_right uu____7396
                                            FStar_Pervasives_Native.snd
                                           in
                                        let uu____7421 =
                                          let uu____7422 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_All.pipe_right uu____7422
                                            FStar_Pervasives_Native.snd
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            (uu___890_7394.FStar_Syntax_Syntax.action_name);
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (uu___890_7394.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (uu___890_7394.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (uu___890_7394.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____7395;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____7421
                                        }) actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.is_layered =
                                     (uu___887_7370.FStar_Syntax_Syntax.is_layered);
                                   FStar_Syntax_Syntax.cattributes =
                                     (uu___887_7370.FStar_Syntax_Syntax.cattributes);
                                   FStar_Syntax_Syntax.mname =
                                     (uu___887_7370.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.univs =
                                     (uu___887_7370.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders =
                                     (uu___887_7370.FStar_Syntax_Syntax.binders);
                                   FStar_Syntax_Syntax.signature = uu____7371;
                                   FStar_Syntax_Syntax.ret_wp = uu____7372;
                                   FStar_Syntax_Syntax.bind_wp = uu____7373;
                                   FStar_Syntax_Syntax.stronger = uu____7374;
                                   FStar_Syntax_Syntax.match_wps = uu____7375;
                                   FStar_Syntax_Syntax.trivial = uu____7380;
                                   FStar_Syntax_Syntax.repr = uu____7383;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____7384;
                                   FStar_Syntax_Syntax.bind_repr = uu____7385;
                                   FStar_Syntax_Syntax.stronger_repr =
                                     FStar_Pervasives_Native.None;
                                   FStar_Syntax_Syntax.actions = uu____7386;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (uu___887_7370.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               ((let uu____7448 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____7448
                                 then
                                   let uu____7453 =
                                     FStar_Syntax_Print.eff_decl_to_string
                                       false ed3
                                      in
                                   FStar_Util.print1
                                     "Typechecked effect declaration:\n\t%s\n"
                                     uu____7453
                                 else ());
                                ed3))))))))))
  
let tc_lex_t :
  'Auu____7470 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____7470 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____7505 = FStar_List.hd ses  in
            uu____7505.FStar_Syntax_Syntax.sigrng  in
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
           | uu____7510 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____7516,[],t,uu____7518,uu____7519);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____7521;
               FStar_Syntax_Syntax.sigattrs = uu____7522;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____7524,_t_top,_lex_t_top,_7558,uu____7527);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____7529;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____7530;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____7532,_t_cons,_lex_t_cons,_7566,uu____7535);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____7537;
                 FStar_Syntax_Syntax.sigattrs = uu____7538;_}::[]
               when
               ((_7558 = Prims.int_zero) && (_7566 = Prims.int_zero)) &&
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
                 let uu____7591 =
                   let uu____7598 =
                     let uu____7599 =
                       let uu____7606 =
                         let uu____7609 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____7609
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____7606, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____7599  in
                   FStar_Syntax_Syntax.mk uu____7598  in
                 uu____7591 FStar_Pervasives_Native.None r1  in
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
                   let uu____7624 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7624
                    in
                 let hd1 =
                   let uu____7626 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7626
                    in
                 let tl1 =
                   let uu____7628 =
                     let uu____7629 =
                       let uu____7636 =
                         let uu____7637 =
                           let uu____7644 =
                             let uu____7647 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____7647
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____7644, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____7637  in
                       FStar_Syntax_Syntax.mk uu____7636  in
                     uu____7629 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7628
                    in
                 let res =
                   let uu____7653 =
                     let uu____7660 =
                       let uu____7661 =
                         let uu____7668 =
                           let uu____7671 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____7671
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____7668,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____7661  in
                     FStar_Syntax_Syntax.mk uu____7660  in
                   uu____7653 FStar_Pervasives_Native.None r2  in
                 let uu____7674 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____7674
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
               let uu____7713 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____7713;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____7718 ->
               let err_msg =
                 let uu____7723 =
                   let uu____7725 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____7725  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____7723
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
    fun uu____7750  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____7750 with
          | (uvs,t) ->
              let uu____7763 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____7763 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____7775 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____7775 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____7793 =
                        let uu____7796 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____7796
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____7793)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7819 =
          let uu____7820 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7820 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7819 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7845 =
          let uu____7846 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7846 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7845 r
  
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
          (let uu____7895 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____7895
           then
             let uu____7898 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____7898
           else ());
          (let uu____7903 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____7903 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____7934 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____7934 FStar_List.flatten  in
               ((let uu____7948 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____7951 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____7951)
                    in
                 if uu____7948
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
                           let uu____7967 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____7977,uu____7978,uu____7979,uu____7980,uu____7981)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____7990 -> failwith "Impossible!"  in
                           match uu____7967 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Inductive type "
                                      (Prims.op_Hat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____8009 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____8019,uu____8020,ty_lid,uu____8022,uu____8023)
                               -> (data_lid, ty_lid)
                           | uu____8030 -> failwith "Impossible"  in
                         match uu____8009 with
                         | (data_lid,ty_lid) ->
                             let uu____8038 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____8041 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____8041)
                                in
                             if uu____8038
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Exception "
                                      (Prims.op_Hat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____8055 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____8060,uu____8061,uu____8062,uu____8063,uu____8064)
                         -> lid
                     | uu____8073 -> failwith "Impossible"  in
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
                   let uu____8091 =
                     (((FStar_List.length tcs) = Prims.int_zero) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____8091
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
          let pop1 uu____8166 =
            let uu____8167 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___1062_8177  ->
               match () with
               | () ->
                   let uu____8184 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____8184 (fun r  -> pop1 (); r)) ()
          with | uu___1061_8215 -> (pop1 (); FStar_Exn.raise uu___1061_8215)
  
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
      | uu____8531 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____8589 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____8589 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____8614 .
    'Auu____8614 FStar_Pervasives_Native.option -> 'Auu____8614 Prims.list
  =
  fun uu___0_8623  ->
    match uu___0_8623 with
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
            let uu____8703 = collect1 tl1  in
            (match uu____8703 with
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
        | ((e,n1)::uu____8941,[]) ->
            FStar_Pervasives_Native.Some (e, n1, Prims.int_zero)
        | ([],(e,n1)::uu____8997) ->
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
          let uu____9207 =
            let uu____9209 = FStar_Options.ide ()  in
            Prims.op_Negation uu____9209  in
          if uu____9207
          then
            let uu____9212 =
              let uu____9217 = FStar_TypeChecker_Env.dsenv env  in
              let uu____9218 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____9217 uu____9218  in
            (match uu____9212 with
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
                              let uu____9251 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____9252 =
                                let uu____9258 =
                                  let uu____9260 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____9262 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____9260 uu____9262
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____9258)
                                 in
                              FStar_Errors.log_issue uu____9251 uu____9252
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____9269 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____9270 =
                                   let uu____9276 =
                                     let uu____9278 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____9278
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____9276)
                                    in
                                 FStar_Errors.log_issue uu____9269 uu____9270)
                              else ())
                         else ())))
          else ()
      | uu____9288 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____9333 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____9361 ->
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
             let uu____9421 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____9421
             then
               let ses1 =
                 let uu____9429 =
                   let uu____9430 =
                     let uu____9431 =
                       tc_inductive
                         (let uu___1194_9440 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1194_9440.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1194_9440.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1194_9440.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1194_9440.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1194_9440.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1194_9440.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1194_9440.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1194_9440.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1194_9440.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1194_9440.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1194_9440.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1194_9440.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1194_9440.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1194_9440.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1194_9440.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1194_9440.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1194_9440.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1194_9440.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1194_9440.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1194_9440.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1194_9440.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___1194_9440.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1194_9440.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1194_9440.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1194_9440.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1194_9440.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1194_9440.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1194_9440.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1194_9440.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1194_9440.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1194_9440.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1194_9440.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1194_9440.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1194_9440.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___1194_9440.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1194_9440.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1194_9440.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1194_9440.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1194_9440.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1194_9440.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1194_9440.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1194_9440.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1194_9440.FStar_TypeChecker_Env.strict_args_tab)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____9431
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____9430
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____9429
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____9454 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____9454
                 then
                   let uu____9459 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1198_9463 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1198_9463.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1198_9463.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1198_9463.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1198_9463.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____9459
                 else ());
                ses1)
             else ses  in
           let uu____9473 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____9473 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___1205_9497 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1205_9497.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1205_9497.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1205_9497.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1205_9497.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____9509 = FStar_TypeChecker_DMFF.cps_and_elaborate env ne
              in
           (match uu____9509 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___1219_9548 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1219_9548.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1219_9548.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1219_9548.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1219_9548.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___1222_9550 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1222_9550.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1222_9550.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1222_9550.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1222_9550.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses), env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           ((let uu____9557 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "LayeredEffects")
                in
             if uu____9557
             then
               let uu____9562 = FStar_Syntax_Print.sigelt_to_string se  in
               FStar_Util.print1
                 "Starting to typecheck layered effect:\n%s\n" uu____9562
             else ());
            (let tc_fun =
               if ne.FStar_Syntax_Syntax.is_layered
               then tc_layered_eff_decl
               else tc_eff_decl  in
             let ne1 =
               let uu____9586 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env)
                  in
               if uu____9586
               then
                 let ne1 =
                   let uu____9590 =
                     let uu____9591 =
                       let uu____9592 =
                         tc_fun
                           (let uu___1232_9595 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1232_9595.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1232_9595.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1232_9595.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1232_9595.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1232_9595.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1232_9595.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1232_9595.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1232_9595.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1232_9595.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1232_9595.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1232_9595.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1232_9595.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1232_9595.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1232_9595.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1232_9595.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1232_9595.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1232_9595.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1232_9595.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1232_9595.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1232_9595.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1232_9595.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 = true;
                              FStar_TypeChecker_Env.failhard =
                                (uu___1232_9595.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1232_9595.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1232_9595.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1232_9595.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1232_9595.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1232_9595.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1232_9595.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1232_9595.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1232_9595.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1232_9595.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1232_9595.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1232_9595.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1232_9595.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___1232_9595.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1232_9595.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1232_9595.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1232_9595.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1232_9595.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1232_9595.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1232_9595.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1232_9595.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1232_9595.FStar_TypeChecker_Env.strict_args_tab)
                            }) ne
                          in
                       FStar_All.pipe_right uu____9592
                         (fun ne1  ->
                            let uu___1235_9601 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_new_effect ne1);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___1235_9601.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___1235_9601.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___1235_9601.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___1235_9601.FStar_Syntax_Syntax.sigattrs)
                            })
                        in
                     FStar_All.pipe_right uu____9591
                       (FStar_TypeChecker_Normalize.elim_uvars env)
                      in
                   FStar_All.pipe_right uu____9590
                     FStar_Syntax_Util.eff_decl_of_new_effect
                    in
                 ((let uu____9603 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "TwoPhases")
                      in
                   if uu____9603
                   then
                     let uu____9608 =
                       FStar_Syntax_Print.sigelt_to_string
                         (let uu___1239_9612 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1239_9612.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1239_9612.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1239_9612.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1239_9612.FStar_Syntax_Syntax.sigattrs)
                          })
                        in
                     FStar_Util.print1 "Effect decl after phase 1: %s\n"
                       uu____9608
                   else ());
                  ne1)
               else ne  in
             let ne2 = tc_fun env ne1  in
             let se1 =
               let uu___1244_9620 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_new_effect ne2);
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1244_9620.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1244_9620.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1244_9620.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1244_9620.FStar_Syntax_Syntax.sigattrs)
               }  in
             ([se1], [], env0)))
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env
               sub1.FStar_Syntax_Syntax.source
              in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env
               sub1.FStar_Syntax_Syntax.target
              in
           if
             ed_src.FStar_Syntax_Syntax.is_layered ||
               ed_tgt.FStar_Syntax_Syntax.is_layered
           then
             let sub2 = tc_layered_lift env0 sub1  in
             ([(let uu___1253_9645 = se  in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                  FStar_Syntax_Syntax.sigrng =
                    (uu___1253_9645.FStar_Syntax_Syntax.sigrng);
                  FStar_Syntax_Syntax.sigquals =
                    (uu___1253_9645.FStar_Syntax_Syntax.sigquals);
                  FStar_Syntax_Syntax.sigmeta =
                    (uu___1253_9645.FStar_Syntax_Syntax.sigmeta);
                  FStar_Syntax_Syntax.sigattrs =
                    (uu___1253_9645.FStar_Syntax_Syntax.sigattrs)
                })], [], env0)
           else
             (let uu____9648 =
                let uu____9655 =
                  FStar_TypeChecker_Env.lookup_effect_lid env
                    sub1.FStar_Syntax_Syntax.source
                   in
                monad_signature env sub1.FStar_Syntax_Syntax.source
                  uu____9655
                 in
              match uu____9648 with
              | (a,wp_a_src) ->
                  let uu____9672 =
                    let uu____9679 =
                      FStar_TypeChecker_Env.lookup_effect_lid env
                        sub1.FStar_Syntax_Syntax.target
                       in
                    monad_signature env sub1.FStar_Syntax_Syntax.target
                      uu____9679
                     in
                  (match uu____9672 with
                   | (b,wp_b_tgt) ->
                       let wp_a_tgt =
                         let uu____9697 =
                           let uu____9700 =
                             let uu____9701 =
                               let uu____9708 =
                                 FStar_Syntax_Syntax.bv_to_name a  in
                               (b, uu____9708)  in
                             FStar_Syntax_Syntax.NT uu____9701  in
                           [uu____9700]  in
                         FStar_Syntax_Subst.subst uu____9697 wp_b_tgt  in
                       let expected_k =
                         let uu____9716 =
                           let uu____9725 = FStar_Syntax_Syntax.mk_binder a
                              in
                           let uu____9732 =
                             let uu____9741 =
                               FStar_Syntax_Syntax.null_binder wp_a_src  in
                             [uu____9741]  in
                           uu____9725 :: uu____9732  in
                         let uu____9766 =
                           FStar_Syntax_Syntax.mk_Total wp_a_tgt  in
                         FStar_Syntax_Util.arrow uu____9716 uu____9766  in
                       let repr_type eff_name a1 wp =
                         (let uu____9788 =
                            let uu____9790 =
                              FStar_TypeChecker_Env.is_reifiable_effect env
                                eff_name
                               in
                            Prims.op_Negation uu____9790  in
                          if uu____9788
                          then
                            let uu____9793 =
                              let uu____9799 =
                                FStar_Util.format1
                                  "Effect %s cannot be reified"
                                  eff_name.FStar_Ident.str
                                 in
                              (FStar_Errors.Fatal_EffectCannotBeReified,
                                uu____9799)
                               in
                            let uu____9803 =
                              FStar_TypeChecker_Env.get_range env  in
                            FStar_Errors.raise_error uu____9793 uu____9803
                          else ());
                         (let uu____9806 =
                            FStar_TypeChecker_Env.effect_decl_opt env
                              eff_name
                             in
                          match uu____9806 with
                          | FStar_Pervasives_Native.None  ->
                              failwith
                                "internal error: reifiable effect has no decl?"
                          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                              let repr =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [FStar_Syntax_Syntax.U_unknown] env ed
                                  ed.FStar_Syntax_Syntax.repr
                                 in
                              let uu____9839 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____9840 =
                                let uu____9847 =
                                  let uu____9848 =
                                    let uu____9865 =
                                      let uu____9876 =
                                        FStar_Syntax_Syntax.as_arg a1  in
                                      let uu____9885 =
                                        let uu____9896 =
                                          FStar_Syntax_Syntax.as_arg wp  in
                                        [uu____9896]  in
                                      uu____9876 :: uu____9885  in
                                    (repr, uu____9865)  in
                                  FStar_Syntax_Syntax.Tm_app uu____9848  in
                                FStar_Syntax_Syntax.mk uu____9847  in
                              uu____9840 FStar_Pervasives_Native.None
                                uu____9839)
                          in
                       let uu____9941 =
                         match ((sub1.FStar_Syntax_Syntax.lift),
                                 (sub1.FStar_Syntax_Syntax.lift_wp))
                         with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.None ) ->
                             failwith "Impossible (parser)"
                         | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp))
                             ->
                             let uu____10114 =
                               if (FStar_List.length uvs) > Prims.int_zero
                               then
                                 let uu____10125 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10125 with
                                 | (usubst,uvs1) ->
                                     let uu____10148 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env uvs1
                                        in
                                     let uu____10149 =
                                       FStar_Syntax_Subst.subst usubst
                                         lift_wp
                                        in
                                     (uu____10148, uu____10149)
                               else (env, lift_wp)  in
                             (match uu____10114 with
                              | (env1,lift_wp1) ->
                                  let lift_wp2 =
                                    if
                                      (FStar_List.length uvs) =
                                        Prims.int_zero
                                    then
                                      check_and_gen env1 lift_wp1 expected_k
                                    else
                                      (let lift_wp2 =
                                         tc_check_trivial_guard env1 lift_wp1
                                           expected_k
                                          in
                                       let uu____10199 =
                                         FStar_Syntax_Subst.close_univ_vars
                                           uvs lift_wp2
                                          in
                                       (uvs, uu____10199))
                                     in
                                  (lift, lift_wp2))
                         | (FStar_Pervasives_Native.Some
                            (what,lift),FStar_Pervasives_Native.None ) ->
                             let uu____10270 =
                               if (FStar_List.length what) > Prims.int_zero
                               then
                                 let uu____10285 =
                                   FStar_Syntax_Subst.univ_var_opening what
                                    in
                                 match uu____10285 with
                                 | (usubst,uvs) ->
                                     let uu____10310 =
                                       FStar_Syntax_Subst.subst usubst lift
                                        in
                                     (uvs, uu____10310)
                               else ([], lift)  in
                             (match uu____10270 with
                              | (uvs,lift1) ->
                                  ((let uu____10346 =
                                      FStar_TypeChecker_Env.debug env
                                        (FStar_Options.Other "ED")
                                       in
                                    if uu____10346
                                    then
                                      let uu____10350 =
                                        FStar_Syntax_Print.term_to_string
                                          lift1
                                         in
                                      FStar_Util.print1
                                        "Lift for free : %s\n" uu____10350
                                    else ());
                                   (let dmff_env =
                                      FStar_TypeChecker_DMFF.empty env
                                        (FStar_TypeChecker_TcTerm.tc_constant
                                           env FStar_Range.dummyRange)
                                       in
                                    let uu____10356 =
                                      let uu____10363 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env uvs
                                         in
                                      FStar_TypeChecker_TcTerm.tc_term
                                        uu____10363 lift1
                                       in
                                    match uu____10356 with
                                    | (lift2,comp,uu____10388) ->
                                        let uu____10389 =
                                          FStar_TypeChecker_DMFF.star_expr
                                            dmff_env lift2
                                           in
                                        (match uu____10389 with
                                         | (uu____10418,lift_wp,lift_elab) ->
                                             let lift_wp1 =
                                               FStar_TypeChecker_DMFF.recheck_debug
                                                 "lift-wp" env lift_wp
                                                in
                                             let lift_elab1 =
                                               FStar_TypeChecker_DMFF.recheck_debug
                                                 "lift-elab" env lift_elab
                                                in
                                             if
                                               (FStar_List.length uvs) =
                                                 Prims.int_zero
                                             then
                                               let uu____10450 =
                                                 let uu____10461 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env lift_elab1
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____10461
                                                  in
                                               let uu____10478 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_wp1
                                                  in
                                               (uu____10450, uu____10478)
                                             else
                                               (let uu____10507 =
                                                  let uu____10518 =
                                                    let uu____10527 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift_elab1
                                                       in
                                                    (uvs, uu____10527)  in
                                                  FStar_Pervasives_Native.Some
                                                    uu____10518
                                                   in
                                                let uu____10542 =
                                                  let uu____10551 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_wp1
                                                     in
                                                  (uvs, uu____10551)  in
                                                (uu____10507, uu____10542))))))
                          in
                       (match uu____9941 with
                        | (lift,lift_wp) ->
                            let env1 =
                              let uu___1324_10625 = env  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___1324_10625.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___1324_10625.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___1324_10625.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___1324_10625.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___1324_10625.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___1324_10625.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___1324_10625.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___1324_10625.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___1324_10625.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___1324_10625.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___1324_10625.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___1324_10625.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___1324_10625.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___1324_10625.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___1324_10625.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___1324_10625.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___1324_10625.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___1324_10625.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___1324_10625.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___1324_10625.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___1324_10625.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 =
                                  (uu___1324_10625.FStar_TypeChecker_Env.phase1);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___1324_10625.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___1324_10625.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___1324_10625.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___1324_10625.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___1324_10625.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___1324_10625.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___1324_10625.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___1324_10625.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___1324_10625.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___1324_10625.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___1324_10625.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___1324_10625.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___1324_10625.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___1324_10625.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___1324_10625.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___1324_10625.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___1324_10625.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___1324_10625.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___1324_10625.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___1324_10625.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___1324_10625.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___1324_10625.FStar_TypeChecker_Env.strict_args_tab)
                              }  in
                            let lift1 =
                              match lift with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None
                              | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                  let uu____10658 =
                                    let uu____10663 =
                                      FStar_Syntax_Subst.univ_var_opening uvs
                                       in
                                    match uu____10663 with
                                    | (usubst,uvs1) ->
                                        let uu____10686 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env1 uvs1
                                           in
                                        let uu____10687 =
                                          FStar_Syntax_Subst.subst usubst
                                            lift1
                                           in
                                        (uu____10686, uu____10687)
                                     in
                                  (match uu____10658 with
                                   | (env2,lift2) ->
                                       let uu____10692 =
                                         let uu____10699 =
                                           FStar_TypeChecker_Env.lookup_effect_lid
                                             env2
                                             sub1.FStar_Syntax_Syntax.source
                                            in
                                         monad_signature env2
                                           sub1.FStar_Syntax_Syntax.source
                                           uu____10699
                                          in
                                       (match uu____10692 with
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
                                                let uu____10725 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env2
                                                   in
                                                let uu____10726 =
                                                  let uu____10733 =
                                                    let uu____10734 =
                                                      let uu____10751 =
                                                        let uu____10762 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            a_typ
                                                           in
                                                        let uu____10771 =
                                                          let uu____10782 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              wp_a_typ
                                                             in
                                                          [uu____10782]  in
                                                        uu____10762 ::
                                                          uu____10771
                                                         in
                                                      (lift_wp1, uu____10751)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10734
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10733
                                                   in
                                                uu____10726
                                                  FStar_Pervasives_Native.None
                                                  uu____10725
                                                 in
                                              repr_type
                                                sub1.FStar_Syntax_Syntax.target
                                                a_typ lift_wp_a
                                               in
                                            let expected_k1 =
                                              let uu____10830 =
                                                let uu____10839 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a1
                                                   in
                                                let uu____10846 =
                                                  let uu____10855 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      wp_a
                                                     in
                                                  let uu____10862 =
                                                    let uu____10871 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        repr_f
                                                       in
                                                    [uu____10871]  in
                                                  uu____10855 :: uu____10862
                                                   in
                                                uu____10839 :: uu____10846
                                                 in
                                              let uu____10902 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  repr_result
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____10830 uu____10902
                                               in
                                            let uu____10905 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k1
                                               in
                                            (match uu____10905 with
                                             | (expected_k2,uu____10915,uu____10916)
                                                 ->
                                                 let lift3 =
                                                   if
                                                     (FStar_List.length uvs)
                                                       = Prims.int_zero
                                                   then
                                                     check_and_gen env2 lift2
                                                       expected_k2
                                                   else
                                                     (let lift3 =
                                                        tc_check_trivial_guard
                                                          env2 lift2
                                                          expected_k2
                                                         in
                                                      let uu____10924 =
                                                        FStar_Syntax_Subst.close_univ_vars
                                                          uvs lift3
                                                         in
                                                      (uvs, uu____10924))
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   lift3)))
                               in
                            ((let uu____10932 =
                                let uu____10934 =
                                  let uu____10936 =
                                    FStar_All.pipe_right lift_wp
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10936
                                    FStar_List.length
                                   in
                                uu____10934 <> Prims.int_one  in
                              if uu____10932
                              then
                                let uu____10959 =
                                  let uu____10965 =
                                    let uu____10967 =
                                      FStar_Syntax_Print.lid_to_string
                                        sub1.FStar_Syntax_Syntax.source
                                       in
                                    let uu____10969 =
                                      FStar_Syntax_Print.lid_to_string
                                        sub1.FStar_Syntax_Syntax.target
                                       in
                                    let uu____10971 =
                                      let uu____10973 =
                                        let uu____10975 =
                                          FStar_All.pipe_right lift_wp
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____10975
                                          FStar_List.length
                                         in
                                      FStar_All.pipe_right uu____10973
                                        FStar_Util.string_of_int
                                       in
                                    FStar_Util.format3
                                      "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                      uu____10967 uu____10969 uu____10971
                                     in
                                  (FStar_Errors.Fatal_TooManyUniverse,
                                    uu____10965)
                                   in
                                FStar_Errors.raise_error uu____10959 r
                              else ());
                             (let uu____11002 =
                                (FStar_Util.is_some lift1) &&
                                  (let uu____11005 =
                                     let uu____11007 =
                                       let uu____11010 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____11010
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____11007
                                       FStar_List.length
                                      in
                                   uu____11005 <> Prims.int_one)
                                 in
                              if uu____11002
                              then
                                let uu____11049 =
                                  let uu____11055 =
                                    let uu____11057 =
                                      FStar_Syntax_Print.lid_to_string
                                        sub1.FStar_Syntax_Syntax.source
                                       in
                                    let uu____11059 =
                                      FStar_Syntax_Print.lid_to_string
                                        sub1.FStar_Syntax_Syntax.target
                                       in
                                    let uu____11061 =
                                      let uu____11063 =
                                        let uu____11065 =
                                          let uu____11068 =
                                            FStar_All.pipe_right lift1
                                              FStar_Util.must
                                             in
                                          FStar_All.pipe_right uu____11068
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____11065
                                          FStar_List.length
                                         in
                                      FStar_All.pipe_right uu____11063
                                        FStar_Util.string_of_int
                                       in
                                    FStar_Util.format3
                                      "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                      uu____11057 uu____11059 uu____11061
                                     in
                                  (FStar_Errors.Fatal_TooManyUniverse,
                                    uu____11055)
                                   in
                                FStar_Errors.raise_error uu____11049 r
                              else ());
                             (let sub2 =
                                let uu___1361_11111 = sub1  in
                                {
                                  FStar_Syntax_Syntax.source =
                                    (uu___1361_11111.FStar_Syntax_Syntax.source);
                                  FStar_Syntax_Syntax.target =
                                    (uu___1361_11111.FStar_Syntax_Syntax.target);
                                  FStar_Syntax_Syntax.lift_wp =
                                    (FStar_Pervasives_Native.Some lift_wp);
                                  FStar_Syntax_Syntax.lift = lift1
                                }  in
                              let se1 =
                                let uu___1364_11113 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1364_11113.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1364_11113.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1364_11113.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1364_11113.FStar_Syntax_Syntax.sigattrs)
                                }  in
                              ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let uu____11127 =
             if (FStar_List.length uvs) = Prims.int_zero
             then (env, uvs, tps, c)
             else
               (let uu____11155 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____11155 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____11186 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____11186 c  in
                    let uu____11195 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____11195, uvs1, tps1, c1))
              in
           (match uu____11127 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____11217 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____11217 with
                 | (tps2,c2) ->
                     let uu____11234 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____11234 with
                      | (tps3,env3,us) ->
                          let uu____11254 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____11254 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____11282)::uu____11283 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____11302 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____11310 =
                                   let uu____11312 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____11312  in
                                 if uu____11310
                                 then
                                   let uu____11315 =
                                     let uu____11321 =
                                       let uu____11323 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____11325 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____11323 uu____11325
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____11321)
                                      in
                                   FStar_Errors.raise_error uu____11315 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____11333 =
                                   let uu____11334 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____11334
                                    in
                                 match uu____11333 with
                                 | (uvs2,t) ->
                                     let uu____11365 =
                                       let uu____11370 =
                                         let uu____11383 =
                                           let uu____11384 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____11384.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____11383)  in
                                       match uu____11370 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____11399,c5)) -> ([], c5)
                                       | (uu____11441,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____11480 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____11365 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               Prims.int_one
                                           then
                                             (let uu____11514 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____11514 with
                                              | (uu____11519,t1) ->
                                                  let uu____11521 =
                                                    let uu____11527 =
                                                      let uu____11529 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____11531 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____11535 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____11529
                                                        uu____11531
                                                        uu____11535
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____11527)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____11521 r)
                                           else ();
                                           (let se1 =
                                              let uu___1434_11542 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___1434_11542.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___1434_11542.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___1434_11542.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___1434_11542.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____11549,uu____11550,uu____11551) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_11556  ->
                   match uu___1_11556 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____11559 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____11565,uu____11566) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_11575  ->
                   match uu___1_11575 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____11578 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____11589 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____11589
             then
               let uu____11592 =
                 let uu____11598 =
                   let uu____11600 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____11600
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____11598)
                  in
               FStar_Errors.raise_error uu____11592 r
             else ());
            (let uu____11606 =
               let uu____11615 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____11615
               then
                 let uu____11626 =
                   tc_declare_typ
                     (let uu___1458_11629 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1458_11629.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1458_11629.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1458_11629.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1458_11629.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1458_11629.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1458_11629.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1458_11629.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1458_11629.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1458_11629.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1458_11629.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1458_11629.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1458_11629.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1458_11629.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1458_11629.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1458_11629.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1458_11629.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1458_11629.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1458_11629.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1458_11629.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1458_11629.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1458_11629.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1458_11629.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1458_11629.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1458_11629.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1458_11629.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1458_11629.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1458_11629.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1458_11629.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1458_11629.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1458_11629.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1458_11629.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1458_11629.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1458_11629.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1458_11629.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1458_11629.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.try_solve_implicits_hook =
                          (uu___1458_11629.FStar_TypeChecker_Env.try_solve_implicits_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1458_11629.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1458_11629.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1458_11629.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1458_11629.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1458_11629.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___1458_11629.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___1458_11629.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1458_11629.FStar_TypeChecker_Env.strict_args_tab)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____11626 with
                 | (uvs1,t1) ->
                     ((let uu____11654 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____11654
                       then
                         let uu____11659 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____11661 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____11659 uu____11661
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____11606 with
             | (uvs1,t1) ->
                 let uu____11696 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____11696 with
                  | (uvs2,t2) ->
                      ([(let uu___1471_11726 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1471_11726.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1471_11726.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1471_11726.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1471_11726.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____11731 =
             let uu____11740 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____11740
             then
               let uu____11751 =
                 tc_assume
                   (let uu___1480_11754 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1480_11754.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1480_11754.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1480_11754.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1480_11754.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1480_11754.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1480_11754.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1480_11754.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1480_11754.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1480_11754.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1480_11754.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1480_11754.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1480_11754.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1480_11754.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1480_11754.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1480_11754.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1480_11754.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1480_11754.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1480_11754.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1480_11754.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1480_11754.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1480_11754.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___1480_11754.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1480_11754.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1480_11754.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1480_11754.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1480_11754.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1480_11754.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1480_11754.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1480_11754.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1480_11754.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1480_11754.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1480_11754.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1480_11754.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1480_11754.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1480_11754.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1480_11754.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1480_11754.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1480_11754.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1480_11754.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1480_11754.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1480_11754.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1480_11754.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1480_11754.FStar_TypeChecker_Env.strict_args_tab)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____11751 with
               | (uvs1,t1) ->
                   ((let uu____11780 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____11780
                     then
                       let uu____11785 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____11787 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____11785
                         uu____11787
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____11731 with
            | (uvs1,t1) ->
                let uu____11822 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____11822 with
                 | (uvs2,t2) ->
                     ([(let uu___1493_11852 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1493_11852.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1493_11852.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1493_11852.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1493_11852.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____11856 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____11856 with
            | (e1,c,g1) ->
                let uu____11876 =
                  let uu____11883 = FStar_TypeChecker_Common.lcomp_comp c  in
                  match uu____11883 with
                  | (c1,g_lc) ->
                      let uu____11896 =
                        let uu____11903 =
                          let uu____11906 =
                            FStar_Syntax_Util.ml_comp
                              FStar_Syntax_Syntax.t_unit r
                             in
                          FStar_Pervasives_Native.Some uu____11906  in
                        FStar_TypeChecker_TcTerm.check_expected_effect env2
                          uu____11903 (e1, c1)
                         in
                      (match uu____11896 with
                       | (e2,_x,g) ->
                           let uu____11916 =
                             FStar_TypeChecker_Env.conj_guard g_lc g  in
                           (e2, _x, uu____11916))
                   in
                (match uu____11876 with
                 | (e2,uu____11928,g) ->
                     ((let uu____11931 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____11931);
                      (let se1 =
                         let uu___1515_11933 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1515_11933.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1515_11933.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1515_11933.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1515_11933.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____11945 = FStar_Options.debug_any ()  in
             if uu____11945
             then
               let uu____11948 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____11950 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____11948
                 uu____11950
             else ());
            (let uu____11955 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____11955 with
             | (t1,uu____11973,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____11987 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____11987 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____11990 =
                              let uu____11996 =
                                let uu____11998 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____12000 =
                                  let uu____12002 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____12002
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____11998 uu____12000
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____11996)
                               in
                            FStar_Errors.raise_error uu____11990 r
                        | uu____12014 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___1536_12019 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1536_12019.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1536_12019.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1536_12019.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1536_12019.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1536_12019.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1536_12019.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1536_12019.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1536_12019.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1536_12019.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1536_12019.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1536_12019.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1536_12019.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1536_12019.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1536_12019.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1536_12019.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1536_12019.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1536_12019.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1536_12019.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1536_12019.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1536_12019.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___1536_12019.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1536_12019.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1536_12019.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1536_12019.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1536_12019.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1536_12019.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1536_12019.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1536_12019.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1536_12019.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1536_12019.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1536_12019.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1536_12019.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1536_12019.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1536_12019.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1536_12019.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1536_12019.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.try_solve_implicits_hook =
                          (uu___1536_12019.FStar_TypeChecker_Env.try_solve_implicits_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1536_12019.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1536_12019.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1536_12019.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1536_12019.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1536_12019.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___1536_12019.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1536_12019.FStar_TypeChecker_Env.strict_args_tab)
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
                 let uu____12087 =
                   let uu____12089 =
                     let uu____12098 = drop_logic val_q  in
                     let uu____12101 = drop_logic q'  in
                     (uu____12098, uu____12101)  in
                   match uu____12089 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____12087
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____12128 =
                      let uu____12134 =
                        let uu____12136 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____12138 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____12140 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____12136 uu____12138 uu____12140
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____12134)
                       in
                    FStar_Errors.raise_error uu____12128 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____12177 =
                   let uu____12178 = FStar_Syntax_Subst.compress def  in
                   uu____12178.FStar_Syntax_Syntax.n  in
                 match uu____12177 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____12190,uu____12191) -> binders
                 | uu____12216 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____12228;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____12333) -> val_bs1
                     | (uu____12364,[]) -> val_bs1
                     | ((body_bv,uu____12396)::bt,(val_bv,aqual)::vt) ->
                         let uu____12453 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____12477) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___1605_12491 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___1607_12494 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___1607_12494.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___1605_12491.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1605_12491.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____12453
                      in
                   let uu____12501 =
                     let uu____12508 =
                       let uu____12509 =
                         let uu____12524 = rename_binders1 def_bs val_bs  in
                         (uu____12524, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____12509  in
                     FStar_Syntax_Syntax.mk uu____12508  in
                   uu____12501 FStar_Pervasives_Native.None r1
               | uu____12543 -> typ1  in
             let uu___1613_12544 = lb  in
             let uu____12545 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___1613_12544.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1613_12544.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____12545;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1613_12544.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___1613_12544.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1613_12544.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1613_12544.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____12548 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____12603  ->
                     fun lb  ->
                       match uu____12603 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____12649 =
                             let uu____12661 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____12661 with
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
                                   | uu____12741 ->
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
                                  (let uu____12788 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____12788, quals_opt1)))
                              in
                           (match uu____12649 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____12548 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____12892 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___2_12898  ->
                                match uu___2_12898 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____12903 -> false))
                         in
                      if uu____12892
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____12916 =
                    let uu____12923 =
                      let uu____12924 =
                        let uu____12938 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____12938)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____12924  in
                    FStar_Syntax_Syntax.mk uu____12923  in
                  uu____12916 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___1656_12957 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1656_12957.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1656_12957.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1656_12957.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1656_12957.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1656_12957.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1656_12957.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1656_12957.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1656_12957.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1656_12957.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1656_12957.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1656_12957.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1656_12957.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1656_12957.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1656_12957.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1656_12957.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1656_12957.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1656_12957.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1656_12957.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1656_12957.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1656_12957.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1656_12957.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1656_12957.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1656_12957.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1656_12957.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1656_12957.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1656_12957.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1656_12957.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1656_12957.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1656_12957.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1656_12957.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1656_12957.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1656_12957.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1656_12957.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1656_12957.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___1656_12957.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1656_12957.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1656_12957.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1656_12957.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1656_12957.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1656_12957.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1656_12957.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1656_12957.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___1656_12957.FStar_TypeChecker_Env.strict_args_tab)
                  }  in
                let e1 =
                  let uu____12960 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____12960
                  then
                    let drop_lbtyp e_lax =
                      let uu____12969 =
                        let uu____12970 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____12970.FStar_Syntax_Syntax.n  in
                      match uu____12969 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____12992 =
                              let uu____12993 = FStar_Syntax_Subst.compress e
                                 in
                              uu____12993.FStar_Syntax_Syntax.n  in
                            match uu____12992 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____12997,lb1::[]),uu____12999) ->
                                let uu____13015 =
                                  let uu____13016 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____13016.FStar_Syntax_Syntax.n  in
                                (match uu____13015 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____13021 -> false)
                            | uu____13023 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___1681_13027 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___1683_13042 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___1683_13042.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___1683_13042.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___1683_13042.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___1683_13042.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___1683_13042.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___1683_13042.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___1681_13027.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___1681_13027.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____13045 -> e_lax  in
                    let uu____13046 =
                      FStar_Util.record_time
                        (fun uu____13054  ->
                           let uu____13055 =
                             let uu____13056 =
                               let uu____13057 =
                                 FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                   (let uu___1687_13066 = env'  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___1687_13066.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___1687_13066.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___1687_13066.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___1687_13066.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___1687_13066.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___1687_13066.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___1687_13066.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___1687_13066.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___1687_13066.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___1687_13066.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___1687_13066.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___1687_13066.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___1687_13066.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___1687_13066.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___1687_13066.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___1687_13066.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___1687_13066.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___1687_13066.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___1687_13066.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___1687_13066.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___1687_13066.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___1687_13066.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___1687_13066.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___1687_13066.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___1687_13066.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___1687_13066.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___1687_13066.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___1687_13066.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___1687_13066.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___1687_13066.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___1687_13066.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___1687_13066.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___1687_13066.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___1687_13066.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___1687_13066.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___1687_13066.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___1687_13066.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___1687_13066.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___1687_13066.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___1687_13066.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___1687_13066.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___1687_13066.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___1687_13066.FStar_TypeChecker_Env.strict_args_tab)
                                    }) e
                                  in
                               FStar_All.pipe_right uu____13057
                                 (fun uu____13079  ->
                                    match uu____13079 with
                                    | (e1,uu____13087,uu____13088) -> e1)
                                in
                             FStar_All.pipe_right uu____13056
                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                  env')
                              in
                           FStar_All.pipe_right uu____13055 drop_lbtyp)
                       in
                    match uu____13046 with
                    | (e1,ms) ->
                        ((let uu____13094 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TwoPhases")
                             in
                          if uu____13094
                          then
                            let uu____13099 =
                              FStar_Syntax_Print.term_to_string e1  in
                            FStar_Util.print1
                              "Let binding after phase 1: %s\n" uu____13099
                          else ());
                         (let uu____13105 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TCDeclTime")
                             in
                          if uu____13105
                          then
                            let uu____13110 = FStar_Util.string_of_int ms  in
                            FStar_Util.print1
                              "Let binding elaborated (phase 1) in %s milliseconds\n"
                              uu____13110
                          else ());
                         e1)
                  else e  in
                let uu____13117 =
                  let uu____13126 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____13126 with
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
                (match uu____13117 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___1717_13231 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___1717_13231.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1717_13231.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1717_13231.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1717_13231.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___1724_13244 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1724_13244.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1724_13244.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___1724_13244.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___1724_13244.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1724_13244.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1724_13244.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____13245 =
                       FStar_Util.record_time
                         (fun uu____13264  ->
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              env' e1)
                        in
                     (match uu____13245 with
                      | (r1,ms) ->
                          ((let uu____13292 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TCDeclTime")
                               in
                            if uu____13292
                            then
                              let uu____13297 = FStar_Util.string_of_int ms
                                 in
                              FStar_Util.print1
                                "Let binding typechecked in phase 2 in %s milliseconds\n"
                                uu____13297
                            else ());
                           (let uu____13302 =
                              match r1 with
                              | ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                                   FStar_Syntax_Syntax.pos = uu____13327;
                                   FStar_Syntax_Syntax.vars = uu____13328;_},uu____13329,g)
                                  when FStar_TypeChecker_Env.is_trivial g ->
                                  let lbs2 =
                                    let uu____13359 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.snd lbs1)
                                        (FStar_List.map rename_parameters)
                                       in
                                    ((FStar_Pervasives_Native.fst lbs1),
                                      uu____13359)
                                     in
                                  let lbs3 =
                                    let uu____13383 =
                                      match post_tau with
                                      | FStar_Pervasives_Native.Some tau ->
                                          FStar_List.map (postprocess_lb tau)
                                            (FStar_Pervasives_Native.snd lbs2)
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.snd lbs2
                                       in
                                    ((FStar_Pervasives_Native.fst lbs2),
                                      uu____13383)
                                     in
                                  let quals1 =
                                    match e2.FStar_Syntax_Syntax.n with
                                    | FStar_Syntax_Syntax.Tm_meta
                                        (uu____13406,FStar_Syntax_Syntax.Meta_desugared
                                         (FStar_Syntax_Syntax.Masked_effect
                                         ))
                                        ->
                                        FStar_Syntax_Syntax.HasMaskedEffect
                                        :: quals
                                    | uu____13411 -> quals  in
                                  ((let uu___1754_13420 = se1  in
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_let
                                           (lbs3, lids));
                                      FStar_Syntax_Syntax.sigrng =
                                        (uu___1754_13420.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals = quals1;
                                      FStar_Syntax_Syntax.sigmeta =
                                        (uu___1754_13420.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (uu___1754_13420.FStar_Syntax_Syntax.sigattrs)
                                    }), lbs3)
                              | uu____13423 ->
                                  failwith
                                    "impossible (typechecking should preserve Tm_let)"
                               in
                            match uu____13302 with
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
                                 (let uu____13479 = log env1  in
                                  if uu____13479
                                  then
                                    let uu____13482 =
                                      let uu____13484 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.snd lbs1)
                                          (FStar_List.map
                                             (fun lb  ->
                                                let should_log =
                                                  let uu____13504 =
                                                    let uu____13513 =
                                                      let uu____13514 =
                                                        let uu____13517 =
                                                          FStar_Util.right
                                                            lb.FStar_Syntax_Syntax.lbname
                                                           in
                                                        uu____13517.FStar_Syntax_Syntax.fv_name
                                                         in
                                                      uu____13514.FStar_Syntax_Syntax.v
                                                       in
                                                    FStar_TypeChecker_Env.try_lookup_val_decl
                                                      env1 uu____13513
                                                     in
                                                  match uu____13504 with
                                                  | FStar_Pervasives_Native.None
                                                       -> true
                                                  | uu____13526 -> false  in
                                                if should_log
                                                then
                                                  let uu____13538 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  let uu____13540 =
                                                    FStar_Syntax_Print.term_to_string
                                                      lb.FStar_Syntax_Syntax.lbtyp
                                                     in
                                                  FStar_Util.format2
                                                    "let %s : %s" uu____13538
                                                    uu____13540
                                                else ""))
                                         in
                                      FStar_All.pipe_right uu____13484
                                        (FStar_String.concat "\n")
                                       in
                                    FStar_Util.print1 "%s\n" uu____13482
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
      (let uu____13592 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____13592
       then
         let uu____13595 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____13595
       else ());
      (let uu____13600 = get_fail_se se  in
       match uu____13600 with
       | FStar_Pervasives_Native.Some (uu____13621,false ) when
           let uu____13638 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____13638 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___1785_13664 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___1785_13664.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___1785_13664.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___1785_13664.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___1785_13664.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___1785_13664.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___1785_13664.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___1785_13664.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___1785_13664.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___1785_13664.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___1785_13664.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___1785_13664.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___1785_13664.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___1785_13664.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___1785_13664.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___1785_13664.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___1785_13664.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___1785_13664.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___1785_13664.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___1785_13664.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___1785_13664.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___1785_13664.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___1785_13664.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___1785_13664.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___1785_13664.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___1785_13664.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___1785_13664.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___1785_13664.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___1785_13664.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___1785_13664.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___1785_13664.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___1785_13664.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___1785_13664.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___1785_13664.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___1785_13664.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___1785_13664.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.try_solve_implicits_hook =
                   (uu___1785_13664.FStar_TypeChecker_Env.try_solve_implicits_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___1785_13664.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___1785_13664.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___1785_13664.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___1785_13664.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___1785_13664.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___1785_13664.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___1785_13664.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___1785_13664.FStar_TypeChecker_Env.strict_args_tab)
               }
             else env1  in
           ((let uu____13669 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____13669
             then
               let uu____13672 =
                 let uu____13674 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____13674
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____13672
             else ());
            (let uu____13688 =
               FStar_Errors.catch_errors
                 (fun uu____13718  ->
                    FStar_Options.with_saved_options
                      (fun uu____13730  -> tc_decl' env' se))
                in
             match uu____13688 with
             | (errs,uu____13742) ->
                 ((let uu____13772 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____13772
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____13807 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____13807  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____13819 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____13830 =
                            let uu____13840 = check_multi_eq errnos1 actual
                               in
                            match uu____13840 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- Prims.int_one), (~- Prims.int_one),
                                  (~- Prims.int_one))
                             in
                          (match uu____13830 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____13905 =
                                   let uu____13911 =
                                     let uu____13913 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____13916 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____13919 =
                                       FStar_Util.string_of_int e  in
                                     let uu____13921 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____13923 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____13913 uu____13916 uu____13919
                                       uu____13921 uu____13923
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____13911)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____13905)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____13950 .
    'Auu____13950 ->
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
               (fun uu___3_13993  ->
                  match uu___3_13993 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____13996 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____14007) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____14015 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____14025 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____14030 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____14046 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____14072 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14098) ->
            let uu____14107 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____14107
            then
              let for_export_bundle se1 uu____14144 =
                match uu____14144 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____14183,uu____14184) ->
                         let dec =
                           let uu___1861_14194 = se1  in
                           let uu____14195 =
                             let uu____14196 =
                               let uu____14203 =
                                 let uu____14204 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____14204  in
                               (l, us, uu____14203)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____14196
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____14195;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1861_14194.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1861_14194.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1861_14194.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____14214,uu____14215,uu____14216) ->
                         let dec =
                           let uu___1872_14224 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1872_14224.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1872_14224.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1872_14224.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____14229 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____14252,uu____14253,uu____14254) ->
            let uu____14255 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____14255 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____14279 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____14279
            then
              ([(let uu___1888_14298 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___1888_14298.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___1888_14298.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___1888_14298.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____14301 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_14307  ->
                         match uu___4_14307 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____14310 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____14316 ->
                             true
                         | uu____14318 -> false))
                  in
               if uu____14301 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____14339 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____14344 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14349 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____14354 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14359 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____14377) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____14391 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____14391
            then ([], hidden)
            else
              (let dec =
                 let uu____14412 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____14412;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____14423 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____14423
            then
              let uu____14434 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1925_14448 = se  in
                        let uu____14449 =
                          let uu____14450 =
                            let uu____14457 =
                              let uu____14458 =
                                let uu____14461 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____14461.FStar_Syntax_Syntax.fv_name  in
                              uu____14458.FStar_Syntax_Syntax.v  in
                            (uu____14457, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____14450  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____14449;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1925_14448.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1925_14448.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1925_14448.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____14434, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____14484 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____14484
       then
         let uu____14487 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____14487
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____14492 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____14510 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
           uu____14527) ->
           let env1 =
             let uu___1946_14532 = env  in
             let uu____14533 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1946_14532.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1946_14532.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1946_14532.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1946_14532.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1946_14532.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1946_14532.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1946_14532.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1946_14532.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1946_14532.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1946_14532.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1946_14532.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1946_14532.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1946_14532.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1946_14532.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1946_14532.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1946_14532.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1946_14532.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1946_14532.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1946_14532.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1946_14532.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1946_14532.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1946_14532.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1946_14532.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1946_14532.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1946_14532.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1946_14532.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1946_14532.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1946_14532.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1946_14532.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1946_14532.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1946_14532.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1946_14532.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1946_14532.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1946_14532.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14533;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1946_14532.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___1946_14532.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1946_14532.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1946_14532.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1946_14532.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1946_14532.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1946_14532.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1946_14532.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1946_14532.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1946_14532.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
           let env1 =
             let uu___1946_14535 = env  in
             let uu____14536 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1946_14535.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1946_14535.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1946_14535.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1946_14535.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1946_14535.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1946_14535.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1946_14535.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1946_14535.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1946_14535.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1946_14535.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1946_14535.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1946_14535.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1946_14535.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1946_14535.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1946_14535.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1946_14535.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1946_14535.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1946_14535.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1946_14535.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1946_14535.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1946_14535.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1946_14535.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1946_14535.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1946_14535.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1946_14535.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1946_14535.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1946_14535.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1946_14535.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1946_14535.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1946_14535.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1946_14535.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1946_14535.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1946_14535.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1946_14535.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14536;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1946_14535.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___1946_14535.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1946_14535.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1946_14535.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1946_14535.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1946_14535.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1946_14535.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1946_14535.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1946_14535.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1946_14535.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions
           uu____14537) ->
           let env1 =
             let uu___1946_14540 = env  in
             let uu____14541 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1946_14540.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1946_14540.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1946_14540.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1946_14540.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1946_14540.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1946_14540.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1946_14540.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1946_14540.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1946_14540.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1946_14540.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1946_14540.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1946_14540.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1946_14540.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1946_14540.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1946_14540.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1946_14540.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1946_14540.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1946_14540.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1946_14540.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1946_14540.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1946_14540.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1946_14540.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1946_14540.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1946_14540.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1946_14540.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1946_14540.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1946_14540.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1946_14540.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1946_14540.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1946_14540.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1946_14540.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1946_14540.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1946_14540.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1946_14540.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14541;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1946_14540.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___1946_14540.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1946_14540.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1946_14540.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1946_14540.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1946_14540.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1946_14540.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1946_14540.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1946_14540.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1946_14540.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____14542) ->
           let env1 =
             let uu___1946_14547 = env  in
             let uu____14548 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1946_14547.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1946_14547.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1946_14547.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1946_14547.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1946_14547.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1946_14547.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1946_14547.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1946_14547.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1946_14547.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1946_14547.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1946_14547.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1946_14547.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1946_14547.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1946_14547.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1946_14547.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1946_14547.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1946_14547.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1946_14547.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1946_14547.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1946_14547.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1946_14547.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1946_14547.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1946_14547.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1946_14547.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1946_14547.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1946_14547.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1946_14547.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1946_14547.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1946_14547.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1946_14547.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1946_14547.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1946_14547.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1946_14547.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1946_14547.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14548;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1946_14547.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___1946_14547.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1946_14547.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1946_14547.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1946_14547.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1946_14547.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1946_14547.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1946_14547.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1946_14547.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1946_14547.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver )
           ->
           ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
              ();
            env)
       | FStar_Syntax_Syntax.Sig_pragma uu____14550 -> env
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14551 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____14561 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____14561) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____14562,uu____14563,uu____14564) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_14569  ->
                   match uu___5_14569 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____14572 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____14574,uu____14575) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_14584  ->
                   match uu___5_14584 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____14587 -> false))
           -> env
       | uu____14589 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____14658 se =
        match uu____14658 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____14711 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____14711
              then
                let uu____14714 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____14714
              else ());
             (let uu____14719 = tc_decl env1 se  in
              match uu____14719 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____14772 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____14772
                             then
                               let uu____14776 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____14776
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____14792 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____14792
                             then
                               let uu____14796 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____14796
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
                    (let uu____14813 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____14813
                     then
                       let uu____14818 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____14827 =
                                  let uu____14829 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____14829 "\n"  in
                                Prims.op_Hat s uu____14827) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____14818
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____14839 =
                       let uu____14848 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____14848
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____14890 se1 =
                            match uu____14890 with
                            | (exports1,hidden1) ->
                                let uu____14918 = for_export env3 hidden1 se1
                                   in
                                (match uu____14918 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____14839 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____15072 = acc  in
        match uu____15072 with
        | (uu____15107,uu____15108,env1,uu____15110) ->
            let r =
              let uu____15144 =
                let uu____15148 =
                  let uu____15150 = FStar_TypeChecker_Env.current_module env1
                     in
                  FStar_Ident.string_of_lid uu____15150  in
                FStar_Pervasives_Native.Some uu____15148  in
              FStar_Profiling.profile
                (fun uu____15173  -> process_one_decl acc se) uu____15144
                "FStar.TypeChecker.Tc.process_one_decl"
               in
            ((let uu____15176 = FStar_Options.profile_group_by_decls ()  in
              if uu____15176
              then
                let tag =
                  match FStar_Syntax_Util.lids_of_sigelt se with
                  | hd1::uu____15183 -> FStar_Ident.string_of_lid hd1
                  | uu____15186 ->
                      FStar_Range.string_of_range
                        (FStar_Syntax_Util.range_of_sigelt se)
                   in
                FStar_Profiling.report_and_clear tag
              else ());
             r)
         in
      let uu____15191 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____15191 with
      | (ses1,exports,env1,uu____15239) ->
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
          let uu___2046_15277 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2046_15277.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2046_15277.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2046_15277.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2046_15277.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2046_15277.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2046_15277.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2046_15277.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2046_15277.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2046_15277.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2046_15277.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___2046_15277.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___2046_15277.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___2046_15277.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2046_15277.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2046_15277.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___2046_15277.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2046_15277.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___2046_15277.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2046_15277.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___2046_15277.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___2046_15277.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___2046_15277.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2046_15277.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2046_15277.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2046_15277.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2046_15277.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2046_15277.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2046_15277.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2046_15277.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2046_15277.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2046_15277.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2046_15277.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2046_15277.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___2046_15277.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2046_15277.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___2046_15277.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2046_15277.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2046_15277.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2046_15277.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2046_15277.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2046_15277.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2046_15277.FStar_TypeChecker_Env.strict_args_tab)
          }  in
        let check_term lid univs1 t =
          let uu____15297 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____15297 with
          | (univs2,t1) ->
              ((let uu____15305 =
                  let uu____15307 =
                    let uu____15313 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____15313  in
                  FStar_All.pipe_left uu____15307
                    (FStar_Options.Other "Exports")
                   in
                if uu____15305
                then
                  let uu____15317 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____15319 =
                    let uu____15321 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____15321
                      (FStar_String.concat ", ")
                     in
                  let uu____15338 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____15317 uu____15319 uu____15338
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____15344 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____15344 (fun a1  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____15370 =
             let uu____15372 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____15374 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____15372 uu____15374
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____15370);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15385) ->
              let uu____15394 =
                let uu____15396 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15396  in
              if uu____15394
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____15410,uu____15411) ->
              let t =
                let uu____15423 =
                  let uu____15430 =
                    let uu____15431 =
                      let uu____15446 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____15446)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____15431  in
                  FStar_Syntax_Syntax.mk uu____15430  in
                uu____15423 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____15462,uu____15463,uu____15464) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____15474 =
                let uu____15476 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15476  in
              if uu____15474 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____15484,lbs),uu____15486) ->
              let uu____15497 =
                let uu____15499 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15499  in
              if uu____15497
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
              let uu____15522 =
                let uu____15524 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15524  in
              if uu____15522
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____15545 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____15546 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____15553 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15554 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____15555 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____15556 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____15563 -> ()  in
        let uu____15564 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____15564 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____15670) -> true
             | uu____15672 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____15702 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____15741 ->
                   let uu____15742 =
                     let uu____15749 =
                       let uu____15750 =
                         let uu____15765 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____15765)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____15750  in
                     FStar_Syntax_Syntax.mk uu____15749  in
                   uu____15742 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____15782,uu____15783) ->
            let s1 =
              let uu___2172_15793 = s  in
              let uu____15794 =
                let uu____15795 =
                  let uu____15802 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____15802)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____15795  in
              let uu____15803 =
                let uu____15806 =
                  let uu____15809 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____15809  in
                FStar_Syntax_Syntax.Assumption :: uu____15806  in
              {
                FStar_Syntax_Syntax.sigel = uu____15794;
                FStar_Syntax_Syntax.sigrng =
                  (uu___2172_15793.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____15803;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2172_15793.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___2172_15793.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____15812 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____15837 lbdef =
        match uu____15837 with
        | (uvs,t) ->
            let attrs =
              let uu____15848 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____15848
              then
                let uu____15853 =
                  let uu____15854 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____15854
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____15853 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___2185_15857 = s  in
            let uu____15858 =
              let uu____15861 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____15861  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___2185_15857.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____15858;
              FStar_Syntax_Syntax.sigmeta =
                (uu___2185_15857.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____15879 -> failwith "Impossible!"  in
        let c_opt =
          let uu____15886 = FStar_Syntax_Util.is_unit t  in
          if uu____15886
          then
            let uu____15893 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____15893
          else
            (let uu____15900 =
               let uu____15901 = FStar_Syntax_Subst.compress t  in
               uu____15901.FStar_Syntax_Syntax.n  in
             match uu____15900 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____15908,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____15932 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____15944 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____15944
            then false
            else
              (let uu____15951 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____15951
               then true
               else
                 (let uu____15958 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____15958))
         in
      let extract_sigelt s =
        (let uu____15970 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____15970
         then
           let uu____15973 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____15973
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____15980 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____16000 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____16019 ->
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
                             (lid,uu____16065,uu____16066,uu____16067,uu____16068,uu____16069)
                             ->
                             ((let uu____16079 =
                                 let uu____16082 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____16082  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____16079);
                              (let uu____16131 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____16131 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____16135,uu____16136,uu____16137,uu____16138,uu____16139)
                             ->
                             ((let uu____16147 =
                                 let uu____16150 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____16150  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____16147);
                              sigelts1)
                         | uu____16199 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____16208 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____16208
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____16218 =
                    let uu___2249_16219 = s  in
                    let uu____16220 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2249_16219.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2249_16219.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____16220;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2249_16219.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2249_16219.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____16218])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____16231 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____16231
             then []
             else
               (let uu____16238 = lbs  in
                match uu____16238 with
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
                        (fun uu____16300  ->
                           match uu____16300 with
                           | (uu____16308,t,uu____16310) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____16327  ->
                             match uu____16327 with
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
                           (fun uu____16354  ->
                              match uu____16354 with
                              | (uu____16362,t,uu____16364) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____16376,uu____16377) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____16385 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____16414 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____16414) uu____16385
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____16418 =
                    let uu___2291_16419 = s  in
                    let uu____16420 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2291_16419.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2291_16419.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____16420;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2291_16419.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2291_16419.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____16418]
                else [])
             else
               (let uu____16427 =
                  let uu___2293_16428 = s  in
                  let uu____16429 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___2293_16428.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___2293_16428.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____16429;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___2293_16428.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___2293_16428.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____16427])
         | FStar_Syntax_Syntax.Sig_new_effect uu____16432 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____16433 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____16434 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____16435 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____16448 -> [s])
         in
      let uu___2305_16449 = m  in
      let uu____16450 =
        let uu____16451 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____16451 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___2305_16449.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____16450;
        FStar_Syntax_Syntax.exports =
          (uu___2305_16449.FStar_Syntax_Syntax.exports);
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
        (fun uu____16502  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____16549  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____16564 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____16564
  
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
      (let uu____16653 = FStar_Options.debug_any ()  in
       if uu____16653
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
         let uu___2330_16669 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___2330_16669.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___2330_16669.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___2330_16669.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___2330_16669.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___2330_16669.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___2330_16669.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___2330_16669.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___2330_16669.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___2330_16669.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___2330_16669.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___2330_16669.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___2330_16669.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___2330_16669.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___2330_16669.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___2330_16669.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___2330_16669.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___2330_16669.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___2330_16669.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___2330_16669.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___2330_16669.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___2330_16669.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___2330_16669.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___2330_16669.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___2330_16669.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___2330_16669.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___2330_16669.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___2330_16669.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___2330_16669.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___2330_16669.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___2330_16669.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___2330_16669.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___2330_16669.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___2330_16669.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___2330_16669.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___2330_16669.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___2330_16669.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___2330_16669.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___2330_16669.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___2330_16669.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___2330_16669.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___2330_16669.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___2330_16669.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___2330_16669.FStar_TypeChecker_Env.strict_args_tab)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____16671 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____16671 with
       | (ses,exports,env3) ->
           ((let uu___2338_16704 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___2338_16704.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___2338_16704.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___2338_16704.FStar_Syntax_Syntax.is_interface)
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
        let uu____16733 = tc_decls env decls  in
        match uu____16733 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___2347_16764 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___2347_16764.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___2347_16764.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___2347_16764.FStar_Syntax_Syntax.is_interface)
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
        let uu____16825 = tc_partial_modul env01 m  in
        match uu____16825 with
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
                (let uu____16862 = FStar_Errors.get_err_count ()  in
                 uu____16862 = Prims.int_zero)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____16873 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____16873
                then
                  let uu____16877 =
                    let uu____16879 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16879 then "" else " (in lax mode) "  in
                  let uu____16887 =
                    let uu____16889 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16889
                    then
                      let uu____16893 =
                        let uu____16895 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.op_Hat uu____16895 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____16893
                    else ""  in
                  let uu____16902 =
                    let uu____16904 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16904
                    then
                      let uu____16908 =
                        let uu____16910 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____16910 "\n"  in
                      Prims.op_Hat "\nto: " uu____16908
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____16877
                    uu____16887 uu____16902
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___2373_16924 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2373_16924.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2373_16924.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2373_16924.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2373_16924.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2373_16924.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2373_16924.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2373_16924.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2373_16924.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2373_16924.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2373_16924.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2373_16924.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2373_16924.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2373_16924.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2373_16924.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2373_16924.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2373_16924.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2373_16924.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2373_16924.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2373_16924.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2373_16924.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2373_16924.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2373_16924.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2373_16924.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2373_16924.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2373_16924.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2373_16924.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2373_16924.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2373_16924.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2373_16924.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2373_16924.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2373_16924.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___2373_16924.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2373_16924.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2373_16924.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2373_16924.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2373_16924.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___2373_16924.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2373_16924.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2373_16924.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2373_16924.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2373_16924.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2373_16924.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2373_16924.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2373_16924.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let en02 =
                    let uu___2376_16926 = en01  in
                    let uu____16927 =
                      let uu____16942 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____16942, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2376_16926.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2376_16926.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2376_16926.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2376_16926.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2376_16926.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2376_16926.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2376_16926.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2376_16926.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2376_16926.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2376_16926.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2376_16926.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2376_16926.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2376_16926.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2376_16926.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2376_16926.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2376_16926.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2376_16926.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2376_16926.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2376_16926.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2376_16926.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2376_16926.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2376_16926.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2376_16926.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2376_16926.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2376_16926.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2376_16926.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2376_16926.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2376_16926.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2376_16926.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2376_16926.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2376_16926.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____16927;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2376_16926.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2376_16926.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2376_16926.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2376_16926.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___2376_16926.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2376_16926.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2376_16926.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2376_16926.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2376_16926.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2376_16926.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___2376_16926.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2376_16926.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2376_16926.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let uu____16988 =
                    let uu____16990 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____16990  in
                  if uu____16988
                  then
                    ((let uu____16994 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____16994 (fun a2  -> ()));
                     en02)
                  else en02  in
                let uu____16998 = tc_modul en0 modul_iface true  in
                match uu____16998 with
                | (modul_iface1,env) ->
                    ((let uu___2385_17011 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___2385_17011.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___2385_17011.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___2385_17011.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___2387_17015 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___2387_17015.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___2387_17015.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___2387_17015.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____17018 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____17018 FStar_Util.smap_clear);
               (let uu____17054 =
                  ((let uu____17058 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____17058) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____17061 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____17061)
                   in
                if uu____17054 then check_exports env modul exports else ());
               (let uu____17067 =
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____17067 (fun a3  -> ()));
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
        let uu____17082 =
          let uu____17084 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____17084  in
        push_context env uu____17082  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____17105 =
                         FStar_TypeChecker_Env.lookup_sigelt env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____17108 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____17108 with | (uu____17115,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____17140 = FStar_Options.debug_any ()  in
         if uu____17140
         then
           let uu____17143 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____17143
         else ());
        (let uu____17155 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____17155
         then
           let uu____17158 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____17158
         else ());
        (let env1 =
           let uu___2417_17164 = env  in
           let uu____17165 =
             let uu____17167 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____17167  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___2417_17164.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___2417_17164.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___2417_17164.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___2417_17164.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___2417_17164.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___2417_17164.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___2417_17164.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___2417_17164.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___2417_17164.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___2417_17164.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___2417_17164.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___2417_17164.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___2417_17164.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___2417_17164.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___2417_17164.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___2417_17164.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___2417_17164.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___2417_17164.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___2417_17164.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___2417_17164.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____17165;
             FStar_TypeChecker_Env.lax_universes =
               (uu___2417_17164.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___2417_17164.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___2417_17164.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___2417_17164.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___2417_17164.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___2417_17164.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___2417_17164.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___2417_17164.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___2417_17164.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___2417_17164.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___2417_17164.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___2417_17164.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___2417_17164.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___2417_17164.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___2417_17164.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___2417_17164.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___2417_17164.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___2417_17164.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___2417_17164.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___2417_17164.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___2417_17164.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___2417_17164.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___2417_17164.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___2417_17164.FStar_TypeChecker_Env.strict_args_tab)
           }  in
         let uu____17169 = tc_modul env1 m b  in
         match uu____17169 with
         | (m1,env2) ->
             ((let uu____17181 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____17181
               then
                 let uu____17184 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____17184
               else ());
              (let uu____17190 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____17190
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
                         let uu____17228 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____17228 with
                         | (univnames1,e) ->
                             let uu___2439_17235 = lb  in
                             let uu____17236 =
                               let uu____17239 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____17239 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2439_17235.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2439_17235.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___2439_17235.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2439_17235.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____17236;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2439_17235.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2439_17235.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___2441_17240 = se  in
                       let uu____17241 =
                         let uu____17242 =
                           let uu____17249 =
                             let uu____17250 = FStar_List.map update lbs  in
                             (b1, uu____17250)  in
                           (uu____17249, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____17242  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____17241;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___2441_17240.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___2441_17240.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___2441_17240.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___2441_17240.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____17258 -> se  in
                 let normalized_module =
                   let uu___2445_17260 = m1  in
                   let uu____17261 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___2445_17260.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____17261;
                     FStar_Syntax_Syntax.exports =
                       (uu___2445_17260.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___2445_17260.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____17262 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____17262
               else ());
              (m1, env2)))
  