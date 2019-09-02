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
  
<<<<<<< HEAD
<<<<<<< HEAD
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
                            let rest_bs =
                              let uu____2280 =
                                let uu____2281 =
                                  FStar_Syntax_Subst.compress ty  in
                                uu____2281.FStar_Syntax_Syntax.n  in
                              match uu____2280 with
                              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____2293)
                                  when
                                  (FStar_List.length bs) >=
                                    (Prims.of_int (2))
                                  ->
                                  let uu____2321 =
                                    FStar_Syntax_Subst.open_binders bs  in
                                  (match uu____2321 with
                                   | (a',uu____2331)::bs1 ->
                                       let uu____2351 =
                                         FStar_List.splitAt
                                           ((FStar_List.length bs1) -
                                              Prims.int_one) bs1
                                          in
                                       (match uu____2351 with
                                        | (bs2,uu____2394) ->
                                            let substs =
                                              let uu____2430 =
                                                let uu____2431 =
                                                  let uu____2438 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a)
                                                     in
                                                  (a', uu____2438)  in
                                                FStar_Syntax_Syntax.NT
                                                  uu____2431
                                                 in
                                              [uu____2430]  in
                                            FStar_Syntax_Subst.subst_binders
                                              substs bs2)
                                   | uu____2445 -> failwith "Impossible!")
                              | uu____2455 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnexpectedEffect, "")
                                    r
                               in
                            let bs = a :: rest_bs  in
                            let uu____2481 =
                              let uu____2492 =
                                let uu____2497 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                let uu____2498 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.fst a)
                                    FStar_Syntax_Syntax.bv_to_name
                                   in
                                fresh_repr r uu____2497 u uu____2498  in
                              match uu____2492 with
                              | (repr1,g) ->
                                  let uu____2513 =
                                    let uu____2520 =
                                      FStar_Syntax_Syntax.gen_bv "f"
                                        FStar_Pervasives_Native.None repr1
                                       in
                                    FStar_All.pipe_right uu____2520
                                      FStar_Syntax_Syntax.mk_binder
                                     in
                                  (uu____2513, g)
                               in
                            (match uu____2481 with
                             | (f,g_f) ->
                                 let uu____2560 =
                                   let uu____2565 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____2566 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____2565 u uu____2566  in
                                 (match uu____2560 with
                                  | (ret_t,g_ret_t) ->
                                      let pure_wp_t =
                                        let pure_wp_ts =
                                          let uu____2585 =
                                            FStar_TypeChecker_Env.lookup_definition
                                              [FStar_TypeChecker_Env.NoDelta]
                                              env
                                              FStar_Parser_Const.pure_wp_lid
                                             in
                                          FStar_All.pipe_right uu____2585
                                            FStar_Util.must
                                           in
                                        let uu____2590 =
                                          FStar_TypeChecker_Env.inst_tscheme
                                            pure_wp_ts
                                           in
                                        match uu____2590 with
                                        | (uu____2595,pure_wp_t) ->
                                            let uu____2597 =
                                              let uu____2602 =
                                                let uu____2603 =
                                                  FStar_All.pipe_right ret_t
                                                    FStar_Syntax_Syntax.as_arg
                                                   in
                                                [uu____2603]  in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                pure_wp_t uu____2602
                                               in
                                            uu____2597
                                              FStar_Pervasives_Native.None r
                                         in
                                      let uu____2636 =
                                        let uu____2649 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs
                                           in
                                        FStar_TypeChecker_Util.new_implicit_var
                                          "" r uu____2649 pure_wp_t
                                         in
                                      (match uu____2636 with
                                       | (pure_wp_uvar,uu____2664,g_pure_wp_uvar)
                                           ->
                                           let c =
                                             let uu____2679 =
                                               let uu____2680 =
                                                 let uu____2681 =
                                                   FStar_TypeChecker_Env.new_u_univ
                                                     ()
                                                    in
                                                 [uu____2681]  in
                                               let uu____2682 =
                                                 let uu____2693 =
                                                   FStar_All.pipe_right
                                                     pure_wp_uvar
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 [uu____2693]  in
                                               {
                                                 FStar_Syntax_Syntax.comp_univs
                                                   = uu____2680;
                                                 FStar_Syntax_Syntax.effect_name
                                                   =
                                                   FStar_Parser_Const.effect_PURE_lid;
                                                 FStar_Syntax_Syntax.result_typ
                                                   = ret_t;
                                                 FStar_Syntax_Syntax.effect_args
                                                   = uu____2682;
                                                 FStar_Syntax_Syntax.flags =
                                                   []
                                               }  in
                                             FStar_Syntax_Syntax.mk_Comp
                                               uu____2679
                                              in
                                           let k =
                                             FStar_Syntax_Util.arrow
                                               (FStar_List.append bs [f]) c
                                              in
                                           ((let uu____2748 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____2748
                                             then
                                               let uu____2753 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected type before unification: %s\n"
                                                 uu____2753
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env
                                                 ty k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env)
                                               [g_f; g_ret_t; g_pure_wp_uvar];
                                             (let k1 =
                                                FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                  env k
                                                 in
                                              let uu____2761 =
                                                let uu____2764 =
                                                  FStar_All.pipe_right k1
                                                    (FStar_TypeChecker_Normalize.normalize
                                                       [FStar_TypeChecker_Env.Beta;
                                                       FStar_TypeChecker_Env.Eager_unfolding]
                                                       env)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2764
                                                  (FStar_Syntax_Subst.close_univ_vars
                                                     stronger_us)
                                                 in
                                              (stronger_us, stronger_t,
                                                uu____2761))))))))))
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
              (let uu____2800 =
                 let uu____2805 =
                   FStar_Syntax_Subst.univ_var_opening
                     act.FStar_Syntax_Syntax.action_univs
                    in
                 match uu____2805 with
                 | (usubst,us) ->
                     let uu____2828 =
                       FStar_TypeChecker_Env.push_univ_vars env us  in
                     let uu____2829 =
                       let uu___339_2830 = act  in
                       let uu____2831 =
                         FStar_Syntax_Subst.subst usubst
                           act.FStar_Syntax_Syntax.action_defn
                          in
                       let uu____2832 =
                         FStar_Syntax_Subst.subst usubst
                           act.FStar_Syntax_Syntax.action_typ
                          in
                       {
                         FStar_Syntax_Syntax.action_name =
                           (uu___339_2830.FStar_Syntax_Syntax.action_name);
                         FStar_Syntax_Syntax.action_unqualified_name =
                           (uu___339_2830.FStar_Syntax_Syntax.action_unqualified_name);
                         FStar_Syntax_Syntax.action_univs = us;
                         FStar_Syntax_Syntax.action_params =
                           (uu___339_2830.FStar_Syntax_Syntax.action_params);
                         FStar_Syntax_Syntax.action_defn = uu____2831;
                         FStar_Syntax_Syntax.action_typ = uu____2832
                       }  in
                     (uu____2828, uu____2829)
                  in
               match uu____2800 with
               | (env1,act1) ->
                   let act_typ =
                     let uu____2836 =
                       let uu____2837 =
                         FStar_Syntax_Subst.compress
                           act1.FStar_Syntax_Syntax.action_typ
                          in
                       uu____2837.FStar_Syntax_Syntax.n  in
                     match uu____2836 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                         let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
                         let uu____2863 =
                           FStar_Ident.lid_equals
                             ct.FStar_Syntax_Syntax.effect_name
                             ed.FStar_Syntax_Syntax.mname
                            in
                         if uu____2863
                         then
                           let repr_ts =
                             let uu____2867 = repr  in
                             match uu____2867 with
                             | (us,t,uu____2882) -> (us, t)  in
                           let repr1 =
                             let uu____2900 =
                               FStar_TypeChecker_Env.inst_tscheme_with
                                 repr_ts ct.FStar_Syntax_Syntax.comp_univs
                                in
                             FStar_All.pipe_right uu____2900
                               FStar_Pervasives_Native.snd
                              in
                           let c1 =
                             let uu____2912 =
                               let uu____2913 =
                                 let uu____2918 =
                                   let uu____2919 =
                                     FStar_Syntax_Syntax.as_arg
                                       ct.FStar_Syntax_Syntax.result_typ
                                      in
                                   uu____2919 ::
                                     (ct.FStar_Syntax_Syntax.effect_args)
                                    in
                                 FStar_Syntax_Syntax.mk_Tm_app repr1
                                   uu____2918
                                  in
                               uu____2913 FStar_Pervasives_Native.None r  in
                             FStar_All.pipe_right uu____2912
                               FStar_Syntax_Syntax.mk_Total
                              in
                           FStar_Syntax_Util.arrow bs c1
                         else act1.FStar_Syntax_Syntax.action_typ
                     | uu____2940 -> act1.FStar_Syntax_Syntax.action_typ  in
                   let uu____2941 =
                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                       act_typ
                      in
                   (match uu____2941 with
                    | (act_typ1,uu____2949,g_t) ->
                        let uu____2951 =
                          let uu____2958 =
                            let uu___363_2959 =
                              FStar_TypeChecker_Env.set_expected_typ env1
                                act_typ1
                               in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___363_2959.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___363_2959.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___363_2959.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___363_2959.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___363_2959.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___363_2959.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___363_2959.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___363_2959.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___363_2959.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___363_2959.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___363_2959.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp = false;
                              FStar_TypeChecker_Env.effects =
                                (uu___363_2959.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___363_2959.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___363_2959.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___363_2959.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___363_2959.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___363_2959.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___363_2959.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___363_2959.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax =
                                (uu___363_2959.FStar_TypeChecker_Env.lax);
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___363_2959.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___363_2959.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___363_2959.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___363_2959.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___363_2959.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___363_2959.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___363_2959.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___363_2959.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___363_2959.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___363_2959.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___363_2959.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___363_2959.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___363_2959.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___363_2959.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
                                (uu___389_3046.FStar_TypeChecker_Env.synth_hook);
=======
                                (uu___387_3128.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___387_3128.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                (uu___363_2959.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___363_2959.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
                              FStar_TypeChecker_Env.splice =
                                (uu___363_2959.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___363_2959.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___363_2959.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___363_2959.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___363_2959.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___363_2959.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___363_2959.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___363_2959.FStar_TypeChecker_Env.strict_args_tab)
                            }  in
                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                            uu____2958 act1.FStar_Syntax_Syntax.action_defn
                           in
                        (match uu____2951 with
                         | (act_defn,uu____2962,g_d) ->
                             ((let uu____2965 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env1)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____2965
                               then
                                 let uu____2970 =
                                   FStar_Syntax_Print.term_to_string act_defn
                                    in
                                 let uu____2972 =
                                   FStar_Syntax_Print.term_to_string act_typ1
                                    in
                                 FStar_Util.print2
                                   "Typechecked action definition: %s and action type: %s\n"
                                   uu____2970 uu____2972
                               else ());
                              (let uu____2977 =
                                 let act_typ2 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Beta] env1
                                     act_typ1
                                    in
                                 let uu____2985 =
                                   let uu____2986 =
                                     FStar_Syntax_Subst.compress act_typ2  in
                                   uu____2986.FStar_Syntax_Syntax.n  in
                                 match uu____2985 with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                     let bs1 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     let env2 =
                                       FStar_TypeChecker_Env.push_binders
                                         env1 bs1
                                        in
                                     let uu____3019 =
                                       FStar_Syntax_Util.type_u ()  in
                                     (match uu____3019 with
                                      | (t,u) ->
                                          let uu____3032 =
                                            FStar_TypeChecker_Util.new_implicit_var
                                              "" r env2 t
                                             in
                                          (match uu____3032 with
                                           | (a_tm,uu____3053,g_tm) ->
                                               let uu____3067 =
                                                 fresh_repr r env2 u a_tm  in
                                               (match uu____3067 with
                                                | (repr1,g) ->
                                                    let uu____3080 =
                                                      let uu____3083 =
                                                        let uu____3086 =
                                                          let uu____3089 =
                                                            FStar_TypeChecker_Env.new_u_univ
                                                              ()
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____3089
                                                            (fun _3092  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _3092)
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total'
                                                          repr1 uu____3086
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____3083
                                                       in
                                                    let uu____3093 =
                                                      FStar_TypeChecker_Env.conj_guard
                                                        g g_tm
                                                       in
                                                    (uu____3080, uu____3093))))
                                 | uu____3096 ->
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                         "") r
                                  in
                               match uu____2977 with
                               | (k,g_k) ->
                                   ((let uu____3112 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other
                                            "LayeredEffects")
                                        in
                                     if uu____3112
                                     then
                                       let uu____3117 =
                                         FStar_Syntax_Print.term_to_string k
                                          in
                                       FStar_Util.print1
                                         "Expected action type: %s\n"
                                         uu____3117
                                     else ());
                                    (let g =
                                       FStar_TypeChecker_Rel.teq env1
                                         act_typ1 k
                                        in
                                     FStar_List.iter
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1) [g_t; g_d; g_k; g];
                                     (let uu____3125 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____3125
                                      then
                                        let uu____3130 =
                                          FStar_Syntax_Print.term_to_string k
                                           in
                                        FStar_Util.print1
                                          "Expected action type after unification: %s\n"
                                          uu____3130
                                      else ());
                                     (let act_typ2 =
                                        let repr_args t =
                                          let uu____3154 =
                                            let uu____3155 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____3155.FStar_Syntax_Syntax.n
                                             in
                                          match uu____3154 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (head1,a::is) ->
                                              let uu____3207 =
                                                let uu____3208 =
                                                  FStar_Syntax_Subst.compress
                                                    head1
                                                   in
                                                uu____3208.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____3207 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (uu____3217,us) ->
                                                   (us,
                                                     (FStar_Pervasives_Native.fst
                                                        a), is)
                                               | uu____3227 ->
                                                   failwith "Impossible!")
                                          | uu____3235 ->
                                              failwith "Impossible!"
                                           in
                                        let k1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Env.Beta] env1
                                            k
                                           in
                                        let uu____3244 =
                                          let uu____3245 =
                                            FStar_Syntax_Subst.compress k1
                                             in
                                          uu____3245.FStar_Syntax_Syntax.n
                                           in
                                        match uu____3244 with
                                        | FStar_Syntax_Syntax.Tm_arrow 
                                            (bs,c) ->
                                            let uu____3270 =
                                              FStar_Syntax_Subst.open_comp bs
                                                c
                                               in
                                            (match uu____3270 with
                                             | (bs1,c1) ->
                                                 let uu____3277 =
                                                   repr_args
                                                     (FStar_Syntax_Util.comp_result
                                                        c1)
                                                    in
                                                 (match uu____3277 with
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
                                                      let uu____3288 =
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          ct
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____3288))
                                        | uu____3291 ->
                                            failwith "Impossible!"
                                         in
                                      (let uu____3294 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____3294
                                       then
                                         let uu____3299 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ2
                                            in
                                         FStar_Util.print1
                                           "Action type after injecting it into the monad: %s\n"
                                           uu____3299
                                       else ());
                                      (let act2 =
                                         if
                                           act1.FStar_Syntax_Syntax.action_univs
                                             = []
                                         then
                                           let uu____3308 =
                                             FStar_TypeChecker_Util.generalize_universes
                                               env1 act_defn
                                              in
                                           match uu____3308 with
                                           | (us,act_defn1) ->
                                               let uu___433_3319 = act1  in
                                               let uu____3320 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   us act_typ2
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___433_3319.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___433_3319.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = us;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___433_3319.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = act_defn1;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = uu____3320
                                               }
                                         else
                                           (let uu___435_3323 = act1  in
                                            let uu____3324 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                act1.FStar_Syntax_Syntax.action_univs
                                                act_defn
                                               in
                                            let uu____3325 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                act1.FStar_Syntax_Syntax.action_univs
                                                act_typ2
                                               in
                                            {
                                              FStar_Syntax_Syntax.action_name
                                                =
                                                (uu___435_3323.FStar_Syntax_Syntax.action_name);
                                              FStar_Syntax_Syntax.action_unqualified_name
                                                =
                                                (uu___435_3323.FStar_Syntax_Syntax.action_unqualified_name);
                                              FStar_Syntax_Syntax.action_univs
                                                =
                                                (uu___435_3323.FStar_Syntax_Syntax.action_univs);
                                              FStar_Syntax_Syntax.action_params
                                                =
                                                (uu___435_3323.FStar_Syntax_Syntax.action_params);
                                              FStar_Syntax_Syntax.action_defn
                                                = uu____3324;
                                              FStar_Syntax_Syntax.action_typ
                                                = uu____3325
                                            })
                                          in
                                       act2)))))))))
               in
            let fst1 uu____3345 =
              match uu____3345 with | (a,uu____3361,uu____3362) -> a  in
            let snd1 uu____3394 =
              match uu____3394 with | (uu____3409,b,uu____3411) -> b  in
            let thd uu____3443 =
              match uu____3443 with | (uu____3458,uu____3459,c) -> c  in
            let uu___453_3473 = ed  in
            let uu____3474 =
              FStar_All.pipe_right
                ((fst1 stronger_repr), (snd1 stronger_repr))
                (fun _3483  -> FStar_Pervasives_Native.Some _3483)
               in
            let uu____3484 =
              FStar_List.map (tc_action env0) ed.FStar_Syntax_Syntax.actions
               in
            {
              FStar_Syntax_Syntax.is_layered =
                (uu___453_3473.FStar_Syntax_Syntax.is_layered);
              FStar_Syntax_Syntax.cattributes =
                (uu___453_3473.FStar_Syntax_Syntax.cattributes);
              FStar_Syntax_Syntax.mname =
                (uu___453_3473.FStar_Syntax_Syntax.mname);
              FStar_Syntax_Syntax.univs =
                (uu___453_3473.FStar_Syntax_Syntax.univs);
              FStar_Syntax_Syntax.binders =
                (uu___453_3473.FStar_Syntax_Syntax.binders);
              FStar_Syntax_Syntax.signature =
                ((fst1 signature), (snd1 signature));
              FStar_Syntax_Syntax.ret_wp =
                ((fst1 return_repr), (thd return_repr));
              FStar_Syntax_Syntax.bind_wp =
                ((fst1 bind_repr), (thd bind_repr));
              FStar_Syntax_Syntax.stronger =
                ((fst1 stronger_repr), (thd stronger_repr));
              FStar_Syntax_Syntax.match_wps =
                (uu___453_3473.FStar_Syntax_Syntax.match_wps);
              FStar_Syntax_Syntax.trivial =
                (uu___453_3473.FStar_Syntax_Syntax.trivial);
              FStar_Syntax_Syntax.repr = ((fst1 repr), (snd1 repr));
              FStar_Syntax_Syntax.return_repr =
                ((fst1 return_repr), (snd1 return_repr));
              FStar_Syntax_Syntax.bind_repr =
                ((fst1 bind_repr), (snd1 bind_repr));
              FStar_Syntax_Syntax.stronger_repr = uu____3474;
              FStar_Syntax_Syntax.actions = uu____3484;
              FStar_Syntax_Syntax.eff_attrs =
                (uu___453_3473.FStar_Syntax_Syntax.eff_attrs)
            }))))))
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____3527 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____3527
       then
         let uu____3532 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____3532
       else ());
      (let uu____3537 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____3537 with
       | (us,lift) ->
           let r = lift.FStar_Syntax_Syntax.pos  in
           (if (FStar_List.length us) <> Prims.int_zero
            then
              (let uu____3571 =
                 let uu____3573 = FStar_Syntax_Print.sub_eff_to_string sub1
                    in
                 Prims.op_Hat
                   "Unexpected number of universes in typechecking %s"
                   uu____3573
                  in
               failwith uu____3571)
            else ();
            (let uu____3578 =
               FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env0 lift  in
             match uu____3578 with
             | (lift1,lc,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env0 g;
                  (let lift_ty =
                     FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                       (FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Beta] env0)
                      in
                   (let uu____3595 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                        (FStar_Options.Other "LayeredEffects")
                       in
                    if uu____3595
                    then
                      let uu____3600 =
                        FStar_Syntax_Print.term_to_string lift1  in
                      let uu____3602 =
                        FStar_Syntax_Print.term_to_string lift_ty  in
                      FStar_Util.print2
                        "Typechecked lift: %s and lift_ty: %s\n" uu____3600
                        uu____3602
                    else ());
                   (let uu____3607 =
                      let uu____3614 =
                        let uu____3619 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____3619
                          (fun uu____3636  ->
                             match uu____3636 with
                             | (t,u) ->
                                 let uu____3647 =
                                   let uu____3648 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t
                                      in
                                   FStar_All.pipe_right uu____3648
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____3647, u))
                         in
                      match uu____3614 with
                      | (a,u_a) ->
                          let uu____3658 =
                            let uu____3665 =
                              FStar_TypeChecker_Env.lookup_effect_lid env0
                                sub1.FStar_Syntax_Syntax.source
                               in
                            monad_signature env0
                              sub1.FStar_Syntax_Syntax.source uu____3665
                             in
                          (match uu____3658 with
                           | (a',wp_sort_a') ->
                               let src_wp_sort_a =
                                 let uu____3679 =
                                   let uu____3682 =
                                     let uu____3683 =
                                       let uu____3690 =
                                         let uu____3693 =
                                           FStar_All.pipe_right a
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_All.pipe_right uu____3693
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       (a', uu____3690)  in
                                     FStar_Syntax_Syntax.NT uu____3683  in
                                   [uu____3682]  in
                                 FStar_Syntax_Subst.subst uu____3679
                                   wp_sort_a'
                                  in
                               let wp =
                                 let uu____3713 =
                                   FStar_Syntax_Syntax.gen_bv "wp"
                                     FStar_Pervasives_Native.None
                                     src_wp_sort_a
                                    in
                                 FStar_All.pipe_right uu____3713
                                   FStar_Syntax_Syntax.mk_binder
                                  in
                               let rest_bs =
                                 let uu____3730 =
                                   let uu____3731 =
                                     FStar_Syntax_Subst.compress lift_ty  in
                                   uu____3731.FStar_Syntax_Syntax.n  in
                                 match uu____3730 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____3743) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (3))
                                     ->
                                     let uu____3771 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____3771 with
                                      | (a'1,uu____3781)::(wp',uu____3783)::bs1
                                          ->
                                          let uu____3813 =
                                            FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 Prims.int_one) bs1
                                             in
                                          (match uu____3813 with
                                           | (bs2,uu____3856) ->
                                               let substs =
                                                 let uu____3892 =
                                                   let uu____3893 =
                                                     let uu____3900 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a)
                                                        in
                                                     (a'1, uu____3900)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____3893
                                                    in
                                                 let uu____3907 =
                                                   let uu____3910 =
                                                     let uu____3911 =
                                                       let uu____3918 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              wp)
                                                          in
                                                       (wp', uu____3918)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____3911
                                                      in
                                                   [uu____3910]  in
                                                 uu____3892 :: uu____3907  in
                                               FStar_Syntax_Subst.subst_binders
                                                 substs bs2)
                                      | uu____3925 -> failwith "Impossible!")
                                 | uu____3935 ->
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_UnexpectedEffect,
                                         "") r
                                  in
                               let f =
                                 let f_sort =
                                   let uu____3956 =
                                     let uu____3965 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_Syntax_Syntax.t_unit
                                        in
                                     [uu____3965]  in
                                   let uu____3984 =
                                     let uu____3987 =
                                       let uu____3988 =
                                         let uu____3991 =
                                           FStar_All.pipe_right a
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_All.pipe_right uu____3991
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       let uu____4002 =
                                         let uu____4013 =
                                           let uu____4022 =
                                             let uu____4023 =
                                               FStar_All.pipe_right wp
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____4023
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           FStar_All.pipe_right uu____4022
                                             FStar_Syntax_Syntax.as_arg
                                            in
                                         [uu____4013]  in
                                       {
                                         FStar_Syntax_Syntax.comp_univs =
                                           [u_a];
                                         FStar_Syntax_Syntax.effect_name =
                                           (sub1.FStar_Syntax_Syntax.source);
                                         FStar_Syntax_Syntax.result_typ =
                                           uu____3988;
                                         FStar_Syntax_Syntax.effect_args =
                                           uu____4002;
                                         FStar_Syntax_Syntax.flags = []
                                       }  in
                                     FStar_Syntax_Syntax.mk_Comp uu____3987
                                      in
                                   FStar_Syntax_Util.arrow uu____3956
                                     uu____3984
                                    in
                                 let uu____4056 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None f_sort
                                    in
                                 FStar_All.pipe_right uu____4056
                                   FStar_Syntax_Syntax.mk_binder
                                  in
                               let bs = a :: wp ::
                                 (FStar_List.append rest_bs [f])  in
                               let uu____4103 =
                                 let uu____4108 =
                                   FStar_TypeChecker_Env.push_binders env0 bs
                                    in
                                 let uu____4109 =
                                   let uu____4110 =
                                     FStar_All.pipe_right a
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____4110
                                     FStar_Syntax_Syntax.bv_to_name
                                    in
                                 FStar_TypeChecker_Util.fresh_layered_effect_repr_en
                                   uu____4108 r
                                   sub1.FStar_Syntax_Syntax.target u_a
                                   uu____4109
                                  in
                               (match uu____4103 with
                                | (repr,g_repr) ->
                                    let uu____4127 =
                                      let uu____4130 =
                                        let uu____4133 =
                                          let uu____4136 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_All.pipe_right uu____4136
                                            (fun _4139  ->
                                               FStar_Pervasives_Native.Some
                                                 _4139)
                                           in
                                        FStar_Syntax_Syntax.mk_Total' repr
                                          uu____4133
                                         in
                                      FStar_Syntax_Util.arrow bs uu____4130
                                       in
                                    (uu____4127, g_repr)))
                       in
                    match uu____3607 with
                    | (k,g_k) ->
                        ((let uu____4149 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____4149
                          then
                            let uu____4154 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print1 "Before unification k: %s\n"
                              uu____4154
                          else ());
                         (let g1 = FStar_TypeChecker_Rel.teq env0 lift_ty k
                             in
                          FStar_TypeChecker_Rel.force_trivial_guard env0 g_k;
                          FStar_TypeChecker_Rel.force_trivial_guard env0 g1;
                          (let uu____4163 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffects")
                              in
                           if uu____4163
                           then
                             let uu____4168 =
                               FStar_Syntax_Print.term_to_string k  in
                             FStar_Util.print1 "After unification k: %s\n"
                               uu____4168
                           else ());
                          (let uu____4173 =
                             FStar_TypeChecker_Util.generalize_universes env0
                               lift1
                              in
                           match uu____4173 with
                           | (us1,lift2) ->
                               let lift_wp =
                                 let uu____4187 =
                                   let uu____4188 =
                                     let uu____4193 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env0 us1
                                        in
                                     FStar_TypeChecker_Normalize.remove_uvar_solutions
                                       uu____4193
                                      in
                                   FStar_All.pipe_right k uu____4188  in
                                 FStar_All.pipe_right uu____4187
                                   (FStar_Syntax_Subst.close_univ_vars us1)
                                  in
                               let sub2 =
                                 let uu___524_4197 = sub1  in
                                 {
                                   FStar_Syntax_Syntax.source =
                                     (uu___524_4197.FStar_Syntax_Syntax.source);
                                   FStar_Syntax_Syntax.target =
                                     (uu___524_4197.FStar_Syntax_Syntax.target);
                                   FStar_Syntax_Syntax.lift_wp =
                                     (FStar_Pervasives_Native.Some
                                        (us1, lift_wp));
                                   FStar_Syntax_Syntax.lift =
                                     (FStar_Pervasives_Native.Some
                                        (us1, lift2))
                                 }  in
                               ((let uu____4207 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env0)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____4207
                                 then
                                   let uu____4212 =
                                     FStar_Syntax_Print.sub_eff_to_string
                                       sub2
                                      in
                                   FStar_Util.print1 "Final sub_effect: %s\n"
                                     uu____4212
                                 else ());
                                sub2))))))))))
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      (let uu____4229 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "ED")
          in
       if uu____4229
       then
         let uu____4234 = FStar_Syntax_Print.eff_decl_to_string false ed  in
         FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____4234
       else ());
      (let uu____4240 =
         let uu____4245 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____4245 with
         | (ed_univs_subst,ed_univs) ->
             let bs =
               let uu____4269 =
                 FStar_Syntax_Subst.subst_binders ed_univs_subst
                   ed.FStar_Syntax_Syntax.binders
                  in
               FStar_Syntax_Subst.open_binders uu____4269  in
             let uu____4270 =
               let uu____4277 =
                 FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
               FStar_TypeChecker_TcTerm.tc_tparams uu____4277 bs  in
             (match uu____4270 with
              | (bs1,uu____4283,uu____4284) ->
                  let uu____4285 =
                    let tmp_t =
                      let uu____4295 =
                        let uu____4298 =
                          FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                            (fun _4303  -> FStar_Pervasives_Native.Some _4303)
                           in
                        FStar_Syntax_Syntax.mk_Total'
                          FStar_Syntax_Syntax.t_unit uu____4298
                         in
                      FStar_Syntax_Util.arrow bs1 uu____4295  in
                    let uu____4304 =
                      FStar_TypeChecker_Util.generalize_universes env0 tmp_t
                       in
                    match uu____4304 with
                    | (us,tmp_t1) ->
                        let uu____4321 =
                          let uu____4322 =
                            let uu____4323 =
                              FStar_All.pipe_right tmp_t1
                                FStar_Syntax_Util.arrow_formals
                               in
                            FStar_All.pipe_right uu____4323
                              FStar_Pervasives_Native.fst
                             in
                          FStar_All.pipe_right uu____4322
                            FStar_Syntax_Subst.close_binders
                           in
                        (us, uu____4321)
                     in
                  (match uu____4285 with
                   | (us,bs2) ->
                       (match ed_univs with
                        | [] -> (us, bs2)
                        | uu____4392 ->
                            let uu____4395 =
                              ((FStar_List.length ed_univs) =
                                 (FStar_List.length us))
                                &&
                                (FStar_List.forall2
                                   (fun u1  ->
                                      fun u2  ->
                                        let uu____4402 =
                                          FStar_Syntax_Syntax.order_univ_name
                                            u1 u2
                                           in
                                        uu____4402 = Prims.int_zero) ed_univs
                                   us)
                               in
                            if uu____4395
                            then (us, bs2)
                            else
                              (let uu____4413 =
                                 let uu____4419 =
                                   let uu____4421 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length ed_univs)
                                      in
                                   let uu____4423 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length us)
                                      in
                                   FStar_Util.format3
                                     "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                     uu____4421 uu____4423
                                    in
                                 (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                   uu____4419)
                                  in
                               let uu____4427 =
                                 FStar_Ident.range_of_lid
                                   ed.FStar_Syntax_Syntax.mname
                                  in
                               FStar_Errors.raise_error uu____4413 uu____4427))))
          in
       match uu____4240 with
       | (us,bs) ->
           let ed1 =
             let uu___556_4435 = ed  in
             {
               FStar_Syntax_Syntax.is_layered =
                 (uu___556_4435.FStar_Syntax_Syntax.is_layered);
               FStar_Syntax_Syntax.cattributes =
                 (uu___556_4435.FStar_Syntax_Syntax.cattributes);
               FStar_Syntax_Syntax.mname =
                 (uu___556_4435.FStar_Syntax_Syntax.mname);
               FStar_Syntax_Syntax.univs = us;
               FStar_Syntax_Syntax.binders = bs;
               FStar_Syntax_Syntax.signature =
                 (uu___556_4435.FStar_Syntax_Syntax.signature);
               FStar_Syntax_Syntax.ret_wp =
                 (uu___556_4435.FStar_Syntax_Syntax.ret_wp);
               FStar_Syntax_Syntax.bind_wp =
                 (uu___556_4435.FStar_Syntax_Syntax.bind_wp);
               FStar_Syntax_Syntax.stronger =
                 (uu___556_4435.FStar_Syntax_Syntax.stronger);
               FStar_Syntax_Syntax.match_wps =
                 (uu___556_4435.FStar_Syntax_Syntax.match_wps);
               FStar_Syntax_Syntax.trivial =
                 (uu___556_4435.FStar_Syntax_Syntax.trivial);
               FStar_Syntax_Syntax.repr =
                 (uu___556_4435.FStar_Syntax_Syntax.repr);
               FStar_Syntax_Syntax.return_repr =
                 (uu___556_4435.FStar_Syntax_Syntax.return_repr);
               FStar_Syntax_Syntax.bind_repr =
                 (uu___556_4435.FStar_Syntax_Syntax.bind_repr);
               FStar_Syntax_Syntax.stronger_repr =
                 (uu___556_4435.FStar_Syntax_Syntax.stronger_repr);
               FStar_Syntax_Syntax.actions =
                 (uu___556_4435.FStar_Syntax_Syntax.actions);
               FStar_Syntax_Syntax.eff_attrs =
                 (uu___556_4435.FStar_Syntax_Syntax.eff_attrs)
             }  in
           let uu____4436 = FStar_Syntax_Subst.univ_var_opening us  in
           (match uu____4436 with
            | (ed_univs_subst,ed_univs) ->
                let uu____4455 =
                  let uu____4460 =
                    FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                  FStar_Syntax_Subst.open_binders' uu____4460  in
                (match uu____4455 with
                 | (ed_bs,ed_bs_subst) ->
                     let ed2 =
                       let op uu____4481 =
                         match uu____4481 with
                         | (us1,t) ->
                             let t1 =
                               let uu____4501 =
                                 FStar_Syntax_Subst.shift_subst
                                   ((FStar_List.length ed_bs) +
                                      (FStar_List.length us1)) ed_univs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____4501 t  in
                             let uu____4510 =
                               let uu____4511 =
                                 FStar_Syntax_Subst.shift_subst
                                   (FStar_List.length us1) ed_bs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____4511 t1  in
                             (us1, uu____4510)
                          in
                       let uu___570_4516 = ed1  in
                       let uu____4517 = op ed1.FStar_Syntax_Syntax.signature
                          in
                       let uu____4518 = op ed1.FStar_Syntax_Syntax.ret_wp  in
                       let uu____4519 = op ed1.FStar_Syntax_Syntax.bind_wp
                          in
                       let uu____4520 = op ed1.FStar_Syntax_Syntax.stronger
                          in
                       let uu____4521 =
                         FStar_Syntax_Util.map_match_wps op
                           ed1.FStar_Syntax_Syntax.match_wps
                          in
                       let uu____4526 =
                         FStar_Util.map_opt ed1.FStar_Syntax_Syntax.trivial
                           op
                          in
                       let uu____4529 = op ed1.FStar_Syntax_Syntax.repr  in
                       let uu____4530 =
                         op ed1.FStar_Syntax_Syntax.return_repr  in
                       let uu____4531 = op ed1.FStar_Syntax_Syntax.bind_repr
                          in
                       let uu____4532 =
                         FStar_List.map
                           (fun a  ->
                              let uu___573_4540 = a  in
                              let uu____4541 =
                                let uu____4542 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_defn))
                                   in
                                FStar_Pervasives_Native.snd uu____4542  in
                              let uu____4553 =
                                let uu____4554 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_typ))
                                   in
                                FStar_Pervasives_Native.snd uu____4554  in
                              {
                                FStar_Syntax_Syntax.action_name =
                                  (uu___573_4540.FStar_Syntax_Syntax.action_name);
                                FStar_Syntax_Syntax.action_unqualified_name =
                                  (uu___573_4540.FStar_Syntax_Syntax.action_unqualified_name);
                                FStar_Syntax_Syntax.action_univs =
                                  (uu___573_4540.FStar_Syntax_Syntax.action_univs);
                                FStar_Syntax_Syntax.action_params =
                                  (uu___573_4540.FStar_Syntax_Syntax.action_params);
                                FStar_Syntax_Syntax.action_defn = uu____4541;
                                FStar_Syntax_Syntax.action_typ = uu____4553
                              }) ed1.FStar_Syntax_Syntax.actions
                          in
                       {
                         FStar_Syntax_Syntax.is_layered =
                           (uu___570_4516.FStar_Syntax_Syntax.is_layered);
                         FStar_Syntax_Syntax.cattributes =
                           (uu___570_4516.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.mname =
                           (uu___570_4516.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.univs =
                           (uu___570_4516.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___570_4516.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature = uu____4517;
                         FStar_Syntax_Syntax.ret_wp = uu____4518;
                         FStar_Syntax_Syntax.bind_wp = uu____4519;
                         FStar_Syntax_Syntax.stronger = uu____4520;
                         FStar_Syntax_Syntax.match_wps = uu____4521;
                         FStar_Syntax_Syntax.trivial = uu____4526;
                         FStar_Syntax_Syntax.repr = uu____4529;
                         FStar_Syntax_Syntax.return_repr = uu____4530;
                         FStar_Syntax_Syntax.bind_repr = uu____4531;
                         FStar_Syntax_Syntax.stronger_repr =
                           FStar_Pervasives_Native.None;
                         FStar_Syntax_Syntax.actions = uu____4532;
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___570_4516.FStar_Syntax_Syntax.eff_attrs)
                       }  in
                     ((let uu____4566 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env0)
                           (FStar_Options.Other "ED")
                          in
                       if uu____4566
                       then
                         let uu____4571 =
                           FStar_Syntax_Print.eff_decl_to_string false ed2
                            in
                         FStar_Util.print1
                           "After typechecking binders eff_decl: \n\t%s\n"
                           uu____4571
                       else ());
                      (let env =
                         let uu____4578 =
                           FStar_TypeChecker_Env.push_univ_vars env0 ed_univs
                            in
                         FStar_TypeChecker_Env.push_binders uu____4578 ed_bs
                          in
                       let check_and_gen' comb n1 env_opt uu____4613 k =
                         match uu____4613 with
                         | (us1,t) ->
                             let env1 =
                               if FStar_Util.is_some env_opt
                               then
                                 FStar_All.pipe_right env_opt FStar_Util.must
                               else env  in
                             let uu____4633 =
                               FStar_Syntax_Subst.open_univ_vars us1 t  in
                             (match uu____4633 with
                              | (us2,t1) ->
                                  let t2 =
                                    match k with
                                    | FStar_Pervasives_Native.Some k1 ->
                                        let uu____4642 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env1 us2
                                           in
                                        tc_check_trivial_guard uu____4642 t1
                                          k1
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____4643 =
                                          let uu____4650 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            uu____4650 t1
                                           in
                                        (match uu____4643 with
                                         | (t2,uu____4652,g) ->
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env1 g;
                                              t2))
                                     in
                                  let uu____4655 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env1 t2
                                     in
                                  (match uu____4655 with
                                   | (g_us,t3) ->
                                       (if (FStar_List.length g_us) <> n1
                                        then
                                          (let error =
                                             let uu____4671 =
                                               FStar_Util.string_of_int n1
                                                in
                                             let uu____4673 =
                                               let uu____4675 =
                                                 FStar_All.pipe_right g_us
                                                   FStar_List.length
                                                  in
                                               FStar_All.pipe_right
                                                 uu____4675
                                                 FStar_Util.string_of_int
                                                in
                                             FStar_Util.format4
                                               "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                               (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                               comb uu____4671 uu____4673
                                              in
                                           FStar_Errors.raise_error
                                             (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                               error)
                                             t3.FStar_Syntax_Syntax.pos)
                                        else ();
                                        (match us2 with
                                         | [] -> (g_us, t3)
                                         | uu____4690 ->
                                             let uu____4691 =
                                               ((FStar_List.length us2) =
                                                  (FStar_List.length g_us))
                                                 &&
                                                 (FStar_List.forall2
                                                    (fun u1  ->
                                                       fun u2  ->
                                                         let uu____4698 =
                                                           FStar_Syntax_Syntax.order_univ_name
                                                             u1 u2
                                                            in
                                                         uu____4698 =
                                                           Prims.int_zero)
                                                    us2 g_us)
                                                in
                                             if uu____4691
                                             then (g_us, t3)
                                             else
                                               (let uu____4709 =
                                                  let uu____4715 =
                                                    let uu____4717 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           us2)
                                                       in
                                                    let uu____4719 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           g_us)
                                                       in
                                                    FStar_Util.format4
                                                      "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                      (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      comb uu____4717
                                                      uu____4719
                                                     in
                                                  (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                    uu____4715)
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4709
                                                  t3.FStar_Syntax_Syntax.pos)))))
                          in
                       let signature =
                         check_and_gen' "signature" Prims.int_one
                           FStar_Pervasives_Native.None
                           ed2.FStar_Syntax_Syntax.signature
                           FStar_Pervasives_Native.None
                          in
                       (let uu____4727 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env0)
                            (FStar_Options.Other "ED")
                           in
                        if uu____4727
                        then
                          let uu____4732 =
                            FStar_Syntax_Print.tscheme_to_string signature
                             in
                          FStar_Util.print1 "Typechecked signature: %s\n"
                            uu____4732
                        else ());
                       (let fresh_a_and_wp uu____4748 =
                          let fail1 t =
                            let uu____4761 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env ed2.FStar_Syntax_Syntax.mname t
                               in
                            FStar_Errors.raise_error uu____4761
                              (FStar_Pervasives_Native.snd
                                 ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                             in
                          let uu____4777 =
                            FStar_TypeChecker_Env.inst_tscheme signature  in
                          match uu____4777 with
                          | (uu____4788,signature1) ->
                              let uu____4790 =
                                let uu____4791 =
                                  FStar_Syntax_Subst.compress signature1  in
                                uu____4791.FStar_Syntax_Syntax.n  in
                              (match uu____4790 with
                               | FStar_Syntax_Syntax.Tm_arrow
                                   (bs1,uu____4801) ->
                                   let bs2 =
                                     FStar_Syntax_Subst.open_binders bs1  in
                                   (match bs2 with
                                    | (a,uu____4830)::(wp,uu____4832)::[] ->
                                        (a, (wp.FStar_Syntax_Syntax.sort))
                                    | uu____4861 -> fail1 signature1)
                               | uu____4862 -> fail1 signature1)
                           in
                        let log_combinator s ts =
                          let uu____4876 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "ED")
                             in
                          if uu____4876
                          then
                            let uu____4881 =
                              FStar_Syntax_Print.tscheme_to_string ts  in
                            FStar_Util.print3 "Typechecked %s:%s = %s\n"
                              (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                              s uu____4881
                          else ()  in
                        let ret_wp =
                          let uu____4887 = fresh_a_and_wp ()  in
                          match uu____4887 with
                          | (a,wp_sort) ->
                              let k =
                                let uu____4903 =
                                  let uu____4912 =
                                    FStar_Syntax_Syntax.mk_binder a  in
                                  let uu____4919 =
                                    let uu____4928 =
                                      let uu____4935 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      FStar_Syntax_Syntax.null_binder
                                        uu____4935
                                       in
                                    [uu____4928]  in
                                  uu____4912 :: uu____4919  in
                                let uu____4954 =
                                  FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                FStar_Syntax_Util.arrow uu____4903 uu____4954
                                 in
                              check_and_gen' "ret_wp" Prims.int_one
                                FStar_Pervasives_Native.None
                                ed2.FStar_Syntax_Syntax.ret_wp
                                (FStar_Pervasives_Native.Some k)
                           in
                        log_combinator "ret_wp" ret_wp;
                        (let bind_wp =
                           let uu____4962 = fresh_a_and_wp ()  in
                           match uu____4962 with
                           | (a,wp_sort_a) ->
                               let uu____4975 = fresh_a_and_wp ()  in
                               (match uu____4975 with
                                | (b,wp_sort_b) ->
                                    let wp_sort_a_b =
                                      let uu____4991 =
                                        let uu____5000 =
                                          let uu____5007 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____5007
                                           in
                                        [uu____5000]  in
                                      let uu____5020 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____4991
                                        uu____5020
                                       in
                                    let k =
                                      let uu____5026 =
                                        let uu____5035 =
                                          FStar_Syntax_Syntax.null_binder
                                            FStar_Syntax_Syntax.t_range
                                           in
                                        let uu____5042 =
                                          let uu____5051 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____5058 =
                                            let uu____5067 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____5074 =
                                              let uu____5083 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              let uu____5090 =
                                                let uu____5099 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a_b
                                                   in
                                                [uu____5099]  in
                                              uu____5083 :: uu____5090  in
                                            uu____5067 :: uu____5074  in
                                          uu____5051 :: uu____5058  in
                                        uu____5035 :: uu____5042  in
                                      let uu____5142 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____5026
                                        uu____5142
                                       in
                                    check_and_gen' "bind_wp"
                                      (Prims.of_int (2))
                                      FStar_Pervasives_Native.None
                                      ed2.FStar_Syntax_Syntax.bind_wp
                                      (FStar_Pervasives_Native.Some k))
                            in
                         log_combinator "bind_wp" bind_wp;
                         (let stronger =
                            let uu____5150 = fresh_a_and_wp ()  in
                            match uu____5150 with
                            | (a,wp_sort_a) ->
                                let uu____5163 = FStar_Syntax_Util.type_u ()
                                   in
                                (match uu____5163 with
                                 | (t,uu____5169) ->
                                     let k =
                                       let uu____5173 =
                                         let uu____5182 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____5189 =
                                           let uu____5198 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____5205 =
                                             let uu____5214 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____5214]  in
                                           uu____5198 :: uu____5205  in
                                         uu____5182 :: uu____5189  in
                                       let uu____5245 =
                                         FStar_Syntax_Syntax.mk_Total t  in
                                       FStar_Syntax_Util.arrow uu____5173
                                         uu____5245
                                        in
                                     check_and_gen' "stronger" Prims.int_one
                                       FStar_Pervasives_Native.None
                                       ed2.FStar_Syntax_Syntax.stronger
                                       (FStar_Pervasives_Native.Some k))
                             in
                          log_combinator "stronger" stronger;
                          (let match_wps =
                             let uu____5257 =
                               FStar_Syntax_Util.get_match_with_close_wps
                                 ed2.FStar_Syntax_Syntax.match_wps
                                in
                             match uu____5257 with
                             | (if_then_else1,ite_wp,close_wp) ->
                                 let if_then_else2 =
                                   let uu____5272 = fresh_a_and_wp ()  in
                                   match uu____5272 with
                                   | (a,wp_sort_a) ->
                                       let p =
                                         let uu____5286 =
                                           let uu____5289 =
                                             FStar_Ident.range_of_lid
                                               ed2.FStar_Syntax_Syntax.mname
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____5289
                                            in
                                         let uu____5290 =
                                           let uu____5291 =
                                             FStar_Syntax_Util.type_u ()  in
                                           FStar_All.pipe_right uu____5291
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____5286 uu____5290
                                          in
                                       let k =
                                         let uu____5303 =
                                           let uu____5312 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____5319 =
                                             let uu____5328 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 p
                                                in
                                             let uu____5335 =
                                               let uu____5344 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               let uu____5351 =
                                                 let uu____5360 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____5360]  in
                                               uu____5344 :: uu____5351  in
                                             uu____5328 :: uu____5335  in
                                           uu____5312 :: uu____5319  in
                                         let uu____5397 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a
                                            in
                                         FStar_Syntax_Util.arrow uu____5303
                                           uu____5397
                                          in
                                       check_and_gen' "if_then_else"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         if_then_else1
                                         (FStar_Pervasives_Native.Some k)
                                    in
                                 (log_combinator "if_then_else" if_then_else2;
                                  (let ite_wp1 =
                                     let uu____5405 = fresh_a_and_wp ()  in
                                     match uu____5405 with
                                     | (a,wp_sort_a) ->
                                         let k =
                                           let uu____5421 =
                                             let uu____5430 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____5437 =
                                               let uu____5446 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____5446]  in
                                             uu____5430 :: uu____5437  in
                                           let uu____5471 =
                                             FStar_Syntax_Syntax.mk_Total
                                               wp_sort_a
                                              in
                                           FStar_Syntax_Util.arrow uu____5421
                                             uu____5471
                                            in
                                         check_and_gen' "ite_wp"
                                           Prims.int_one
                                           FStar_Pervasives_Native.None
                                           ite_wp
                                           (FStar_Pervasives_Native.Some k)
                                      in
                                   log_combinator "ite_wp" ite_wp1;
                                   (let close_wp1 =
                                      let uu____5479 = fresh_a_and_wp ()  in
                                      match uu____5479 with
                                      | (a,wp_sort_a) ->
                                          let b =
                                            let uu____5493 =
                                              let uu____5496 =
                                                FStar_Ident.range_of_lid
                                                  ed2.FStar_Syntax_Syntax.mname
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____5496
                                               in
                                            let uu____5497 =
                                              let uu____5498 =
                                                FStar_Syntax_Util.type_u ()
                                                 in
                                              FStar_All.pipe_right uu____5498
                                                FStar_Pervasives_Native.fst
                                               in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____5493 uu____5497
                                             in
                                          let wp_sort_b_a =
                                            let uu____5510 =
                                              let uu____5519 =
                                                let uu____5526 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    b
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____5526
                                                 in
                                              [uu____5519]  in
                                            let uu____5539 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____5510 uu____5539
                                             in
                                          let k =
                                            let uu____5545 =
                                              let uu____5554 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____5561 =
                                                let uu____5570 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    b
                                                   in
                                                let uu____5577 =
                                                  let uu____5586 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_b_a
                                                     in
                                                  [uu____5586]  in
                                                uu____5570 :: uu____5577  in
                                              uu____5554 :: uu____5561  in
                                            let uu____5617 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____5545 uu____5617
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
                             let uu____5627 = fresh_a_and_wp ()  in
                             match uu____5627 with
                             | (a,wp_sort_a) ->
                                 let uu____5642 = FStar_Syntax_Util.type_u ()
                                    in
                                 (match uu____5642 with
                                  | (t,uu____5650) ->
                                      let k =
                                        let uu____5654 =
                                          let uu____5663 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____5670 =
                                            let uu____5679 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_sort_a
                                               in
                                            [uu____5679]  in
                                          uu____5663 :: uu____5670  in
                                        let uu____5704 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____5654
                                          uu____5704
                                         in
                                      let trivial =
                                        let uu____5708 =
                                          FStar_All.pipe_right
                                            ed2.FStar_Syntax_Syntax.trivial
                                            FStar_Util.must
                                           in
                                        check_and_gen' "trivial"
                                          Prims.int_one
                                          FStar_Pervasives_Native.None
                                          uu____5708
                                          (FStar_Pervasives_Native.Some k)
                                         in
                                      (log_combinator "trivial" trivial;
                                       FStar_Pervasives_Native.Some trivial))
                              in
                           let uu____5723 =
                             let uu____5734 =
                               let uu____5735 =
                                 FStar_Syntax_Subst.compress
                                   (FStar_Pervasives_Native.snd
                                      ed2.FStar_Syntax_Syntax.repr)
                                  in
                               uu____5735.FStar_Syntax_Syntax.n  in
                             match uu____5734 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____5754 ->
                                 let repr =
                                   let uu____5756 = fresh_a_and_wp ()  in
                                   match uu____5756 with
                                   | (a,wp_sort_a) ->
                                       let uu____5769 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____5769 with
                                        | (t,uu____5775) ->
                                            let k =
                                              let uu____5779 =
                                                let uu____5788 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____5795 =
                                                  let uu____5804 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a
                                                     in
                                                  [uu____5804]  in
                                                uu____5788 :: uu____5795  in
                                              let uu____5829 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____5779 uu____5829
                                               in
                                            check_and_gen' "repr"
                                              Prims.int_one
                                              FStar_Pervasives_Native.None
                                              ed2.FStar_Syntax_Syntax.repr
                                              (FStar_Pervasives_Native.Some k))
                                    in
                                 (log_combinator "repr" repr;
                                  (let mk_repr' t wp =
                                     let uu____5849 =
                                       FStar_TypeChecker_Env.inst_tscheme
                                         repr
                                        in
                                     match uu____5849 with
                                     | (uu____5856,repr1) ->
                                         let repr2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.EraseUniverses;
                                             FStar_TypeChecker_Env.AllowUnboundUniverses]
                                             env repr1
                                            in
                                         let uu____5859 =
                                           let uu____5866 =
                                             let uu____5867 =
                                               let uu____5884 =
                                                 let uu____5895 =
                                                   FStar_All.pipe_right t
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____5912 =
                                                   let uu____5923 =
                                                     FStar_All.pipe_right wp
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____5923]  in
                                                 uu____5895 :: uu____5912  in
                                               (repr2, uu____5884)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5867
                                              in
                                           FStar_Syntax_Syntax.mk uu____5866
                                            in
                                         uu____5859
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                      in
                                   let mk_repr a wp =
                                     let uu____5989 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     mk_repr' uu____5989 wp  in
                                   let destruct_repr t =
                                     let uu____6004 =
                                       let uu____6005 =
                                         FStar_Syntax_Subst.compress t  in
                                       uu____6005.FStar_Syntax_Syntax.n  in
                                     match uu____6004 with
                                     | FStar_Syntax_Syntax.Tm_app
                                         (uu____6016,(t1,uu____6018)::
                                          (wp,uu____6020)::[])
                                         -> (t1, wp)
                                     | uu____6079 ->
                                         failwith "Unexpected repr type"
                                      in
                                   let return_repr =
                                     let uu____6090 = fresh_a_and_wp ()  in
                                     match uu____6090 with
                                     | (a,uu____6098) ->
                                         let x_a =
                                           let uu____6104 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x_a"
                                             FStar_Pervasives_Native.None
                                             uu____6104
                                            in
                                         let res =
                                           let wp =
                                             let uu____6112 =
                                               let uu____6117 =
                                                 let uu____6118 =
                                                   FStar_TypeChecker_Env.inst_tscheme
                                                     ret_wp
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____6118
                                                   FStar_Pervasives_Native.snd
                                                  in
                                               let uu____6127 =
                                                 let uu____6128 =
                                                   let uu____6137 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6137
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____6146 =
                                                   let uu____6157 =
                                                     let uu____6166 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         x_a
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____6166
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____6157]  in
                                                 uu____6128 :: uu____6146  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____6117 uu____6127
                                                in
                                             uu____6112
                                               FStar_Pervasives_Native.None
                                               FStar_Range.dummyRange
                                              in
                                           mk_repr a wp  in
                                         let k =
                                           let uu____6202 =
                                             let uu____6211 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____6218 =
                                               let uu____6227 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   x_a
                                                  in
                                               [uu____6227]  in
                                             uu____6211 :: uu____6218  in
                                           let uu____6252 =
                                             FStar_Syntax_Syntax.mk_Total res
                                              in
                                           FStar_Syntax_Util.arrow uu____6202
                                             uu____6252
                                            in
                                         let uu____6255 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env k
                                            in
                                         (match uu____6255 with
                                          | (k1,uu____6263,uu____6264) ->
                                              let env1 =
                                                let uu____6268 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env
                                                    (FStar_Pervasives_Native.snd
                                                       ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____6268
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
                                        let uu____6279 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            FStar_Parser_Const.range_0
                                            FStar_Syntax_Syntax.delta_constant
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_All.pipe_right uu____6279
                                          FStar_Syntax_Syntax.fv_to_tm
                                         in
                                      let uu____6280 = fresh_a_and_wp ()  in
                                      match uu____6280 with
                                      | (a,wp_sort_a) ->
                                          let uu____6293 = fresh_a_and_wp ()
                                             in
                                          (match uu____6293 with
                                           | (b,wp_sort_b) ->
                                               let wp_sort_a_b =
                                                 let uu____6309 =
                                                   let uu____6318 =
                                                     let uu____6325 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____6325
                                                      in
                                                   [uu____6318]  in
                                                 let uu____6338 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     wp_sort_b
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____6309 uu____6338
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
                                                 let uu____6346 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     a
                                                    in
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "x_a"
                                                   FStar_Pervasives_Native.None
                                                   uu____6346
                                                  in
                                               let wp_g_x =
                                                 let uu____6351 =
                                                   let uu____6356 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       wp_g
                                                      in
                                                   let uu____6357 =
                                                     let uu____6358 =
                                                       let uu____6367 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x_a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____6367
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____6358]  in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     uu____6356 uu____6357
                                                    in
                                                 uu____6351
                                                   FStar_Pervasives_Native.None
                                                   FStar_Range.dummyRange
                                                  in
                                               let res =
                                                 let wp =
                                                   let uu____6398 =
                                                     let uu____6403 =
                                                       let uu____6404 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           bind_wp
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____6404
                                                         FStar_Pervasives_Native.snd
                                                        in
                                                     let uu____6413 =
                                                       let uu____6414 =
                                                         let uu____6417 =
                                                           let uu____6420 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               a
                                                              in
                                                           let uu____6421 =
                                                             let uu____6424 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 b
                                                                in
                                                             let uu____6425 =
                                                               let uu____6428
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_f
                                                                  in
                                                               let uu____6429
                                                                 =
                                                                 let uu____6432
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g
                                                                    in
                                                                 [uu____6432]
                                                                  in
                                                               uu____6428 ::
                                                                 uu____6429
                                                                in
                                                             uu____6424 ::
                                                               uu____6425
                                                              in
                                                           uu____6420 ::
                                                             uu____6421
                                                            in
                                                         r :: uu____6417  in
                                                       FStar_List.map
                                                         FStar_Syntax_Syntax.as_arg
                                                         uu____6414
                                                        in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____6403 uu____6413
                                                      in
                                                   uu____6398
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 mk_repr b wp  in
                                               let maybe_range_arg =
                                                 let uu____6450 =
                                                   FStar_Util.for_some
                                                     (FStar_Syntax_Util.attr_eq
                                                        FStar_Syntax_Util.dm4f_bind_range_attr)
                                                     ed2.FStar_Syntax_Syntax.eff_attrs
                                                    in
                                                 if uu____6450
                                                 then
                                                   let uu____6461 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       FStar_Syntax_Syntax.t_range
                                                      in
                                                   let uu____6468 =
                                                     let uu____6477 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         FStar_Syntax_Syntax.t_range
                                                        in
                                                     [uu____6477]  in
                                                   uu____6461 :: uu____6468
                                                 else []  in
                                               let k =
                                                 let uu____6513 =
                                                   let uu____6522 =
                                                     let uu____6531 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6538 =
                                                       let uu____6547 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           b
                                                          in
                                                       [uu____6547]  in
                                                     uu____6531 :: uu____6538
                                                      in
                                                   let uu____6572 =
                                                     let uu____6581 =
                                                       let uu____6590 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           wp_f
                                                          in
                                                       let uu____6597 =
                                                         let uu____6606 =
                                                           let uu____6613 =
                                                             let uu____6614 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp_f
                                                                in
                                                             mk_repr a
                                                               uu____6614
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____6613
                                                            in
                                                         let uu____6615 =
                                                           let uu____6624 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               wp_g
                                                              in
                                                           let uu____6631 =
                                                             let uu____6640 =
                                                               let uu____6647
                                                                 =
                                                                 let uu____6648
                                                                   =
                                                                   let uu____6657
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                   [uu____6657]
                                                                    in
                                                                 let uu____6676
                                                                   =
                                                                   let uu____6679
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                   FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____6679
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   uu____6648
                                                                   uu____6676
                                                                  in
                                                               FStar_Syntax_Syntax.null_binder
                                                                 uu____6647
                                                                in
                                                             [uu____6640]  in
                                                           uu____6624 ::
                                                             uu____6631
                                                            in
                                                         uu____6606 ::
                                                           uu____6615
                                                          in
                                                       uu____6590 ::
                                                         uu____6597
                                                        in
                                                     FStar_List.append
                                                       maybe_range_arg
                                                       uu____6581
                                                      in
                                                   FStar_List.append
                                                     uu____6522 uu____6572
                                                    in
                                                 let uu____6724 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     res
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____6513 uu____6724
                                                  in
                                               let uu____6727 =
                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                   env k
                                                  in
                                               (match uu____6727 with
                                                | (k1,uu____6735,uu____6736)
                                                    ->
                                                    let env1 =
                                                      FStar_TypeChecker_Env.set_range
                                                        env
                                                        (FStar_Pervasives_Native.snd
                                                           ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                       in
                                                    let env2 =
                                                      FStar_All.pipe_right
                                                        (let uu___771_6748 =
                                                           env1  in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.instantiate_imp);
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             = true;
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
<<<<<<< HEAD
<<<<<<< HEAD
                                                             (uu___797_6835.FStar_TypeChecker_Env.synth_hook);
=======
                                                             (uu___795_6917.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.try_solve_implicits_hook
                                                             =
                                                             (uu___795_6917.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                                             (uu___771_6748.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.try_solve_implicits_hook
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.nbe);
                                                           FStar_TypeChecker_Env.strict_args_tab
                                                             =
                                                             (uu___771_6748.FStar_TypeChecker_Env.strict_args_tab)
                                                         })
                                                        (fun _6750  ->
                                                           FStar_Pervasives_Native.Some
                                                             _6750)
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
                                         (let uu____6777 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env, act)
                                            else
                                              (let uu____6791 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____6791 with
                                               | (usubst,uvs) ->
                                                   let uu____6814 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env uvs
                                                      in
                                                   let uu____6815 =
                                                     let uu___784_6816 = act
                                                        in
                                                     let uu____6817 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____6818 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___784_6816.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___784_6816.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___784_6816.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____6817;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____6818
                                                     }  in
                                                   (uu____6814, uu____6815))
                                             in
                                          match uu____6777 with
                                          | (env1,act1) ->
                                              let act_typ =
                                                let uu____6822 =
                                                  let uu____6823 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  uu____6823.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____6822 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs1,c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c
                                                       in
                                                    let uu____6849 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname
                                                       in
                                                    if uu____6849
                                                    then
                                                      let uu____6852 =
                                                        let uu____6855 =
                                                          let uu____6856 =
                                                            let uu____6857 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____6857
                                                             in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____6856
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____6855
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____6852
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____6880 ->
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              let uu____6881 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env1 act_typ
                                                 in
                                              (match uu____6881 with
                                               | (act_typ1,uu____6889,g_t) ->
                                                   let env' =
                                                     let uu___801_6892 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env1 act_typ1
                                                        in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_sig
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.gamma_sig);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.attrtab
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.attrtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.phase1
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.phase1);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.uvar_subtyping
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.uvar_subtyping);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.fv_delta_depths
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.fv_delta_depths);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
<<<<<<< HEAD
<<<<<<< HEAD
                                                         (uu___827_6979.FStar_TypeChecker_Env.synth_hook);
=======
                                                         (uu___825_7061.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.try_solve_implicits_hook
                                                         =
                                                         (uu___825_7061.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                                         (uu___801_6892.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.try_solve_implicits_hook
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.postprocess
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.postprocess);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.nbe
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.nbe);
                                                       FStar_TypeChecker_Env.strict_args_tab
                                                         =
                                                         (uu___801_6892.FStar_TypeChecker_Env.strict_args_tab)
                                                     }  in
                                                   ((let uu____6895 =
                                                       FStar_TypeChecker_Env.debug
                                                         env1
                                                         (FStar_Options.Other
                                                            "ED")
                                                        in
                                                     if uu____6895
                                                     then
                                                       let uu____6899 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name
                                                          in
                                                       let uu____6901 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____6903 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1
                                                          in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____6899
                                                         uu____6901
                                                         uu____6903
                                                     else ());
                                                    (let uu____6908 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     match uu____6908 with
                                                     | (act_defn,uu____6916,g_a)
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
                                                         let uu____6920 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2
                                                              in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs1,c) ->
                                                               let uu____6956
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs1 c
                                                                  in
                                                               (match uu____6956
                                                                with
                                                                | (bs2,uu____6968)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____6975
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____6975
                                                                     in
                                                                    let uu____6978
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____6978
                                                                    with
                                                                    | 
                                                                    (k1,uu____6992,g)
                                                                    ->
                                                                    (k1, g)))
                                                           | uu____6996 ->
                                                               let uu____6997
                                                                 =
                                                                 let uu____7003
                                                                   =
                                                                   let uu____7005
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                   let uu____7007
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____7005
                                                                    uu____7007
                                                                    in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____7003)
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____6997
                                                                 act_defn1.FStar_Syntax_Syntax.pos
                                                            in
                                                         (match uu____6920
                                                          with
                                                          | (expected_k,g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env1
                                                                  act_typ2
                                                                  expected_k
                                                                 in
                                                              ((let uu____7025
                                                                  =
                                                                  let uu____7026
                                                                    =
                                                                    let uu____7027
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____7027
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____7026
                                                                   in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env1
                                                                  uu____7025);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____7029
                                                                    =
                                                                    let uu____7030
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____7030.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____7029
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____7055
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____7055
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____7062
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____7062
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____7082
                                                                    =
                                                                    let uu____7083
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____7083]
                                                                     in
                                                                    let uu____7084
                                                                    =
                                                                    let uu____7095
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____7095]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____7082;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____7084;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____7120
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____7120))
                                                                  | uu____7123
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                   in
                                                                let uu____7125
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
                                                                    let uu____7147
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____7147))
                                                                   in
                                                                match uu____7125
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
                                                                    let uu___851_7166
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___851_7166.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___851_7166.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___851_7166.FStar_Syntax_Syntax.action_params);
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
                           match uu____5723 with
                           | (repr,return_repr,bind_repr,actions) ->
                               let cl ts =
                                 let ts1 =
                                   FStar_Syntax_Subst.close_tscheme ed_bs ts
                                    in
                                 let ed_univs_closing =
                                   FStar_Syntax_Subst.univ_var_closing
                                     ed_univs
                                    in
                                 let uu____7191 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length ed_bs)
                                     ed_univs_closing
                                    in
                                 FStar_Syntax_Subst.subst_tscheme uu____7191
                                   ts1
                                  in
                               let ed3 =
                                 let uu___863_7201 = ed2  in
                                 let uu____7202 = cl signature  in
                                 let uu____7203 = cl ret_wp  in
                                 let uu____7204 = cl bind_wp  in
                                 let uu____7205 = cl stronger  in
                                 let uu____7206 =
                                   FStar_Syntax_Util.map_match_wps cl
                                     match_wps
                                    in
                                 let uu____7211 =
                                   FStar_Util.map_opt trivial cl  in
                                 let uu____7214 = cl repr  in
                                 let uu____7215 = cl return_repr  in
                                 let uu____7216 = cl bind_repr  in
                                 let uu____7217 =
                                   FStar_List.map
                                     (fun a  ->
                                        let uu___866_7225 = a  in
                                        let uu____7226 =
                                          let uu____7227 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_All.pipe_right uu____7227
                                            FStar_Pervasives_Native.snd
                                           in
                                        let uu____7252 =
                                          let uu____7253 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_All.pipe_right uu____7253
                                            FStar_Pervasives_Native.snd
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            (uu___866_7225.FStar_Syntax_Syntax.action_name);
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (uu___866_7225.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (uu___866_7225.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (uu___866_7225.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____7226;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____7252
                                        }) actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.is_layered =
                                     (uu___863_7201.FStar_Syntax_Syntax.is_layered);
                                   FStar_Syntax_Syntax.cattributes =
                                     (uu___863_7201.FStar_Syntax_Syntax.cattributes);
                                   FStar_Syntax_Syntax.mname =
                                     (uu___863_7201.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.univs =
                                     (uu___863_7201.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders =
                                     (uu___863_7201.FStar_Syntax_Syntax.binders);
                                   FStar_Syntax_Syntax.signature = uu____7202;
                                   FStar_Syntax_Syntax.ret_wp = uu____7203;
                                   FStar_Syntax_Syntax.bind_wp = uu____7204;
                                   FStar_Syntax_Syntax.stronger = uu____7205;
                                   FStar_Syntax_Syntax.match_wps = uu____7206;
                                   FStar_Syntax_Syntax.trivial = uu____7211;
                                   FStar_Syntax_Syntax.repr = uu____7214;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____7215;
                                   FStar_Syntax_Syntax.bind_repr = uu____7216;
                                   FStar_Syntax_Syntax.stronger_repr =
                                     FStar_Pervasives_Native.None;
                                   FStar_Syntax_Syntax.actions = uu____7217;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (uu___863_7201.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               ((let uu____7279 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____7279
                                 then
                                   let uu____7284 =
                                     FStar_Syntax_Print.eff_decl_to_string
                                       false ed3
                                      in
                                   FStar_Util.print1
                                     "Typechecked effect declaration:\n\t%s\n"
                                     uu____7284
                                 else ());
                                ed3))))))))))
  
=======
>>>>>>> snap
=======
>>>>>>> snap
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
                (let skip_prims_type uu____803 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____808,uu____809,uu____810,uu____811,uu____812)
                         -> lid
                     | uu____821 -> failwith "Impossible"  in
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
                   let uu____839 =
                     (((FStar_List.length tcs) = Prims.int_zero) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____839
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
          let pop1 uu____914 =
            let uu____915 = FStar_TypeChecker_Env.pop env1 "tc_inductive"  in
            ()  in
          try
            (fun uu___200_925  ->
               match () with
               | () ->
                   let uu____932 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____932 (fun r  -> pop1 (); r)) ()
          with | uu___199_963 -> (pop1 (); FStar_Exn.raise uu___199_963)
  
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
      | uu____1279 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____1337 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____1337 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____1362 .
    'Auu____1362 FStar_Pervasives_Native.option -> 'Auu____1362 Prims.list
  =
  fun uu___0_1371  ->
    match uu___0_1371 with
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
            let uu____1451 = collect1 tl1  in
            (match uu____1451 with
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
        | ((e,n1)::uu____1689,[]) ->
            FStar_Pervasives_Native.Some (e, n1, Prims.int_zero)
        | ([],(e,n1)::uu____1745) ->
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
          let uu____1955 =
            let uu____1957 = FStar_Options.ide ()  in
            Prims.op_Negation uu____1957  in
          if uu____1955
          then
            let uu____1960 =
              let uu____1965 = FStar_TypeChecker_Env.dsenv env  in
              let uu____1966 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____1965 uu____1966  in
            (match uu____1960 with
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
                              let uu____1999 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____2000 =
                                let uu____2006 =
                                  let uu____2008 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____2010 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____2008 uu____2010
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____2006)
                                 in
                              FStar_Errors.log_issue uu____1999 uu____2000
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____2017 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____2018 =
                                   let uu____2024 =
                                     let uu____2026 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____2026
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____2024)
                                    in
                                 FStar_Errors.log_issue uu____2017 uu____2018)
                              else ())
                         else ())))
          else ()
      | uu____2036 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____2081 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____2109 ->
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
             let uu____2169 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____2169
             then
               let ses1 =
                 let uu____2177 =
                   let uu____2178 =
                     let uu____2179 =
                       tc_inductive
                         (let uu___332_2188 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___332_2188.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___332_2188.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___332_2188.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___332_2188.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___332_2188.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___332_2188.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___332_2188.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___332_2188.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___332_2188.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___332_2188.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___332_2188.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___332_2188.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___332_2188.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___332_2188.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___332_2188.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___332_2188.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___332_2188.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___332_2188.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___332_2188.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___332_2188.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___332_2188.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___332_2188.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___332_2188.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___332_2188.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___332_2188.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___332_2188.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___332_2188.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___332_2188.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___332_2188.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___332_2188.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___332_2188.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___332_2188.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___332_2188.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                              (uu___1196_9358.FStar_TypeChecker_Env.synth_hook);
=======
                              (uu___1194_9440.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___1194_9440.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                              (uu___1170_9271.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___1170_9271.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                              (uu___332_2188.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___332_2188.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                              (uu___332_2188.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___332_2188.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
                            FStar_TypeChecker_Env.splice =
                              (uu___332_2188.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___332_2188.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___332_2188.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___332_2188.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___332_2188.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___332_2188.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___332_2188.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___332_2188.FStar_TypeChecker_Env.strict_args_tab)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____2179
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____2178
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____2177
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____2202 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____2202
                 then
                   let uu____2207 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___336_2211 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___336_2211.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___336_2211.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___336_2211.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___336_2211.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____2207
                 else ());
                ses1)
             else ses  in
           let uu____2221 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____2221 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___343_2245 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___343_2245.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___343_2245.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___343_2245.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___343_2245.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____2257 =
             FStar_TypeChecker_TcEffect.dmff_cps_and_elaborate env ne  in
           (match uu____2257 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___357_2296 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___357_2296.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___357_2296.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___357_2296.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___357_2296.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___360_2298 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___360_2298.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___360_2298.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___360_2298.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___360_2298.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses), env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 =
             let uu____2305 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env)
                in
             if uu____2305
             then
<<<<<<< HEAD
               let uu____9393 = FStar_Syntax_Print.sigelt_to_string se  in
               FStar_Util.print1
                 "Starting to typecheck layered effect:\n%s\n" uu____9393
             else ());
            (let tc_fun =
               if ne.FStar_Syntax_Syntax.is_layered
               then tc_layered_eff_decl
               else tc_eff_decl  in
             let ne1 =
               let uu____9417 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env)
                  in
               if uu____9417
               then
                 let ne1 =
                   let uu____9421 =
                     let uu____9422 =
                       let uu____9423 =
                         tc_fun
                           (let uu___1208_9426 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1208_9426.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1208_9426.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1208_9426.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1208_9426.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1208_9426.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1208_9426.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1208_9426.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1208_9426.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1208_9426.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1208_9426.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1208_9426.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1208_9426.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1208_9426.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1208_9426.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1208_9426.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1208_9426.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1208_9426.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1208_9426.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1208_9426.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1208_9426.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1208_9426.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 = true;
                              FStar_TypeChecker_Env.failhard =
                                (uu___1208_9426.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1208_9426.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1208_9426.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1208_9426.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1208_9426.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1208_9426.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1208_9426.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1208_9426.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1208_9426.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1208_9426.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1208_9426.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1208_9426.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
                                (uu___1234_9513.FStar_TypeChecker_Env.synth_hook);
=======
                                (uu___1232_9595.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___1232_9595.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                (uu___1208_9426.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___1208_9426.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
                              FStar_TypeChecker_Env.splice =
                                (uu___1208_9426.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1208_9426.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1208_9426.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1208_9426.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1208_9426.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1208_9426.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1208_9426.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1208_9426.FStar_TypeChecker_Env.strict_args_tab)
                            }) ne
                          in
                       FStar_All.pipe_right uu____9423
                         (fun ne1  ->
                            let uu___1211_9432 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_new_effect ne1);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___1211_9432.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___1211_9432.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___1211_9432.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___1211_9432.FStar_Syntax_Syntax.sigattrs)
                            })
=======
               let ne1 =
                 let uu____2309 =
                   let uu____2310 =
                     let uu____2311 =
                       FStar_TypeChecker_TcEffect.tc_eff_decl
                         (let uu___366_2314 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___366_2314.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___366_2314.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___366_2314.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___366_2314.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___366_2314.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___366_2314.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___366_2314.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___366_2314.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___366_2314.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___366_2314.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___366_2314.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___366_2314.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___366_2314.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___366_2314.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___366_2314.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___366_2314.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___366_2314.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___366_2314.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___366_2314.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___366_2314.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___366_2314.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___366_2314.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___366_2314.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___366_2314.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___366_2314.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___366_2314.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___366_2314.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___366_2314.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___366_2314.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___366_2314.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___366_2314.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___366_2314.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___366_2314.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___366_2314.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___366_2314.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___366_2314.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___366_2314.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___366_2314.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___366_2314.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___366_2314.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___366_2314.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___366_2314.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___366_2314.FStar_TypeChecker_Env.strict_args_tab)
                          }) ne
>>>>>>> snap
                        in
                     FStar_All.pipe_right uu____2311
                       (fun ne1  ->
                          let uu___369_2320 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___369_2320.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___369_2320.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___369_2320.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___369_2320.FStar_Syntax_Syntax.sigattrs)
                          })
                      in
                   FStar_All.pipe_right uu____2310
                     (FStar_TypeChecker_Normalize.elim_uvars env)
                    in
                 FStar_All.pipe_right uu____2309
                   FStar_Syntax_Util.eff_decl_of_new_effect
                  in
               ((let uu____2322 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____2322
                 then
                   let uu____2327 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___373_2331 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___373_2331.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___373_2331.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___373_2331.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___373_2331.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Effect decl after phase 1: %s\n"
                     uu____2327
                 else ());
                ne1)
             else ne  in
           let ne2 = FStar_TypeChecker_TcEffect.tc_eff_decl env ne1  in
           let se1 =
             let uu___378_2339 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne2);
               FStar_Syntax_Syntax.sigrng =
                 (uu___378_2339.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___378_2339.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___378_2339.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___378_2339.FStar_Syntax_Syntax.sigattrs)
             }  in
           ([se1], [], env0)
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
<<<<<<< HEAD
<<<<<<< HEAD
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
             ([(let uu___1229_9476 = se  in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                  FStar_Syntax_Syntax.sigrng =
                    (uu___1229_9476.FStar_Syntax_Syntax.sigrng);
                  FStar_Syntax_Syntax.sigquals =
                    (uu___1229_9476.FStar_Syntax_Syntax.sigquals);
                  FStar_Syntax_Syntax.sigmeta =
                    (uu___1229_9476.FStar_Syntax_Syntax.sigmeta);
                  FStar_Syntax_Syntax.sigattrs =
                    (uu___1229_9476.FStar_Syntax_Syntax.sigattrs)
                })], [], env0)
           else
             (let uu____9479 =
                let uu____9486 =
                  FStar_TypeChecker_Env.lookup_effect_lid env
                    sub1.FStar_Syntax_Syntax.source
                   in
                monad_signature env sub1.FStar_Syntax_Syntax.source
                  uu____9486
                 in
              match uu____9479 with
              | (a,wp_a_src) ->
                  let uu____9503 =
                    let uu____9510 =
                      FStar_TypeChecker_Env.lookup_effect_lid env
                        sub1.FStar_Syntax_Syntax.target
                       in
                    monad_signature env sub1.FStar_Syntax_Syntax.target
                      uu____9510
                     in
                  (match uu____9503 with
                   | (b,wp_b_tgt) ->
                       let wp_a_tgt =
                         let uu____9528 =
                           let uu____9531 =
                             let uu____9532 =
                               let uu____9539 =
                                 FStar_Syntax_Syntax.bv_to_name a  in
                               (b, uu____9539)  in
                             FStar_Syntax_Syntax.NT uu____9532  in
                           [uu____9531]  in
                         FStar_Syntax_Subst.subst uu____9528 wp_b_tgt  in
                       let expected_k =
                         let uu____9547 =
                           let uu____9556 = FStar_Syntax_Syntax.mk_binder a
                              in
                           let uu____9563 =
                             let uu____9572 =
                               FStar_Syntax_Syntax.null_binder wp_a_src  in
                             [uu____9572]  in
                           uu____9556 :: uu____9563  in
                         let uu____9597 =
                           FStar_Syntax_Syntax.mk_Total wp_a_tgt  in
                         FStar_Syntax_Util.arrow uu____9547 uu____9597  in
                       let repr_type eff_name a1 wp =
                         (let uu____9619 =
                            let uu____9621 =
                              FStar_TypeChecker_Env.is_reifiable_effect env
                                eff_name
                               in
                            Prims.op_Negation uu____9621  in
                          if uu____9619
                          then
                            let uu____9624 =
                              let uu____9630 =
                                FStar_Util.format1
                                  "Effect %s cannot be reified"
                                  eff_name.FStar_Ident.str
                                 in
                              (FStar_Errors.Fatal_EffectCannotBeReified,
                                uu____9630)
                               in
                            let uu____9634 =
                              FStar_TypeChecker_Env.get_range env  in
                            FStar_Errors.raise_error uu____9624 uu____9634
                          else ());
                         (let uu____9637 =
                            FStar_TypeChecker_Env.effect_decl_opt env
                              eff_name
                             in
                          match uu____9637 with
                          | FStar_Pervasives_Native.None  ->
                              failwith
                                "internal error: reifiable effect has no decl?"
                          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                              let repr =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [FStar_Syntax_Syntax.U_unknown] env ed
                                  ed.FStar_Syntax_Syntax.repr
                                 in
                              let uu____9670 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____9671 =
                                let uu____9678 =
                                  let uu____9679 =
                                    let uu____9696 =
                                      let uu____9707 =
                                        FStar_Syntax_Syntax.as_arg a1  in
                                      let uu____9716 =
                                        let uu____9727 =
                                          FStar_Syntax_Syntax.as_arg wp  in
                                        [uu____9727]  in
                                      uu____9707 :: uu____9716  in
                                    (repr, uu____9696)  in
                                  FStar_Syntax_Syntax.Tm_app uu____9679  in
                                FStar_Syntax_Syntax.mk uu____9678  in
                              uu____9671 FStar_Pervasives_Native.None
                                uu____9670)
                          in
                       let uu____9772 =
                         match ((sub1.FStar_Syntax_Syntax.lift),
                                 (sub1.FStar_Syntax_Syntax.lift_wp))
                         with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.None ) ->
                             failwith "Impossible (parser)"
                         | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp))
                             ->
                             let uu____9945 =
                               if (FStar_List.length uvs) > Prims.int_zero
                               then
                                 let uu____9956 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____9956 with
                                 | (usubst,uvs1) ->
                                     let uu____9979 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env uvs1
                                        in
                                     let uu____9980 =
                                       FStar_Syntax_Subst.subst usubst
                                         lift_wp
                                        in
                                     (uu____9979, uu____9980)
                               else (env, lift_wp)  in
                             (match uu____9945 with
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
                                       let uu____10030 =
                                         FStar_Syntax_Subst.close_univ_vars
                                           uvs lift_wp2
                                          in
                                       (uvs, uu____10030))
                                     in
                                  (lift, lift_wp2))
                         | (FStar_Pervasives_Native.Some
                            (what,lift),FStar_Pervasives_Native.None ) ->
                             let uu____10101 =
                               if (FStar_List.length what) > Prims.int_zero
                               then
                                 let uu____10116 =
                                   FStar_Syntax_Subst.univ_var_opening what
                                    in
                                 match uu____10116 with
                                 | (usubst,uvs) ->
                                     let uu____10141 =
                                       FStar_Syntax_Subst.subst usubst lift
                                        in
                                     (uvs, uu____10141)
                               else ([], lift)  in
                             (match uu____10101 with
                              | (uvs,lift1) ->
                                  ((let uu____10177 =
                                      FStar_TypeChecker_Env.debug env
                                        (FStar_Options.Other "ED")
                                       in
                                    if uu____10177
                                    then
                                      let uu____10181 =
                                        FStar_Syntax_Print.term_to_string
                                          lift1
                                         in
                                      FStar_Util.print1
                                        "Lift for free : %s\n" uu____10181
                                    else ());
                                   (let dmff_env =
                                      FStar_TypeChecker_DMFF.empty env
                                        (FStar_TypeChecker_TcTerm.tc_constant
                                           env FStar_Range.dummyRange)
                                       in
                                    let uu____10187 =
                                      let uu____10194 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env uvs
                                         in
                                      FStar_TypeChecker_TcTerm.tc_term
                                        uu____10194 lift1
                                       in
                                    match uu____10187 with
                                    | (lift2,comp,uu____10219) ->
                                        let uu____10220 =
                                          FStar_TypeChecker_DMFF.star_expr
                                            dmff_env lift2
                                           in
                                        (match uu____10220 with
                                         | (uu____10249,lift_wp,lift_elab) ->
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
                                               let uu____10281 =
                                                 let uu____10292 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env lift_elab1
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____10292
                                                  in
                                               let uu____10309 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_wp1
                                                  in
                                               (uu____10281, uu____10309)
                                             else
                                               (let uu____10338 =
                                                  let uu____10349 =
                                                    let uu____10358 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift_elab1
                                                       in
                                                    (uvs, uu____10358)  in
                                                  FStar_Pervasives_Native.Some
                                                    uu____10349
                                                   in
                                                let uu____10373 =
                                                  let uu____10382 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_wp1
                                                     in
                                                  (uvs, uu____10382)  in
                                                (uu____10338, uu____10373))))))
                          in
                       (match uu____9772 with
                        | (lift,lift_wp) ->
                            let env1 =
                              let uu___1300_10456 = env  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___1300_10456.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___1300_10456.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___1300_10456.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___1300_10456.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___1300_10456.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___1300_10456.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___1300_10456.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___1300_10456.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___1300_10456.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___1300_10456.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___1300_10456.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___1300_10456.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___1300_10456.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___1300_10456.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___1300_10456.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___1300_10456.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___1300_10456.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___1300_10456.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___1300_10456.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___1300_10456.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___1300_10456.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 =
                                  (uu___1300_10456.FStar_TypeChecker_Env.phase1);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___1300_10456.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___1300_10456.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___1300_10456.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___1300_10456.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___1300_10456.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___1300_10456.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___1300_10456.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___1300_10456.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___1300_10456.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___1300_10456.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___1300_10456.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___1300_10456.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
                                  (uu___1326_10543.FStar_TypeChecker_Env.synth_hook);
=======
                                  (uu___1324_10625.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___1324_10625.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                  (uu___1300_10456.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___1300_10456.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
                                FStar_TypeChecker_Env.splice =
                                  (uu___1300_10456.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___1300_10456.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___1300_10456.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___1300_10456.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___1300_10456.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___1300_10456.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___1300_10456.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___1300_10456.FStar_TypeChecker_Env.strict_args_tab)
                              }  in
                            let lift1 =
                              match lift with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None
                              | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                  let uu____10489 =
                                    let uu____10494 =
                                      FStar_Syntax_Subst.univ_var_opening uvs
                                       in
                                    match uu____10494 with
                                    | (usubst,uvs1) ->
                                        let uu____10517 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env1 uvs1
                                           in
                                        let uu____10518 =
                                          FStar_Syntax_Subst.subst usubst
                                            lift1
                                           in
                                        (uu____10517, uu____10518)
                                     in
                                  (match uu____10489 with
                                   | (env2,lift2) ->
                                       let uu____10523 =
                                         let uu____10530 =
                                           FStar_TypeChecker_Env.lookup_effect_lid
                                             env2
                                             sub1.FStar_Syntax_Syntax.source
                                            in
                                         monad_signature env2
                                           sub1.FStar_Syntax_Syntax.source
                                           uu____10530
                                          in
                                       (match uu____10523 with
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
                                                let uu____10556 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env2
                                                   in
                                                let uu____10557 =
                                                  let uu____10564 =
                                                    let uu____10565 =
                                                      let uu____10582 =
                                                        let uu____10593 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            a_typ
                                                           in
                                                        let uu____10602 =
                                                          let uu____10613 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              wp_a_typ
                                                             in
                                                          [uu____10613]  in
                                                        uu____10593 ::
                                                          uu____10602
                                                         in
                                                      (lift_wp1, uu____10582)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10565
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10564
                                                   in
                                                uu____10557
                                                  FStar_Pervasives_Native.None
                                                  uu____10556
                                                 in
                                              repr_type
                                                sub1.FStar_Syntax_Syntax.target
                                                a_typ lift_wp_a
                                               in
                                            let expected_k1 =
                                              let uu____10661 =
                                                let uu____10670 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a1
                                                   in
                                                let uu____10677 =
                                                  let uu____10686 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      wp_a
                                                     in
                                                  let uu____10693 =
                                                    let uu____10702 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        repr_f
                                                       in
                                                    [uu____10702]  in
                                                  uu____10686 :: uu____10693
                                                   in
                                                uu____10670 :: uu____10677
                                                 in
                                              let uu____10733 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  repr_result
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____10661 uu____10733
                                               in
                                            let uu____10736 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k1
                                               in
                                            (match uu____10736 with
                                             | (expected_k2,uu____10746,uu____10747)
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
                                                      let uu____10755 =
                                                        FStar_Syntax_Subst.close_univ_vars
                                                          uvs lift3
                                                         in
                                                      (uvs, uu____10755))
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   lift3)))
                               in
                            ((let uu____10763 =
                                let uu____10765 =
                                  let uu____10767 =
                                    FStar_All.pipe_right lift_wp
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10767
                                    FStar_List.length
                                   in
                                uu____10765 <> Prims.int_one  in
                              if uu____10763
                              then
                                let uu____10790 =
                                  let uu____10796 =
                                    let uu____10798 =
                                      FStar_Syntax_Print.lid_to_string
                                        sub1.FStar_Syntax_Syntax.source
                                       in
                                    let uu____10800 =
                                      FStar_Syntax_Print.lid_to_string
                                        sub1.FStar_Syntax_Syntax.target
                                       in
                                    let uu____10802 =
                                      let uu____10804 =
                                        let uu____10806 =
                                          FStar_All.pipe_right lift_wp
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____10806
                                          FStar_List.length
                                         in
                                      FStar_All.pipe_right uu____10804
                                        FStar_Util.string_of_int
                                       in
                                    FStar_Util.format3
                                      "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                      uu____10798 uu____10800 uu____10802
                                     in
                                  (FStar_Errors.Fatal_TooManyUniverse,
                                    uu____10796)
                                   in
                                FStar_Errors.raise_error uu____10790 r
                              else ());
                             (let uu____10833 =
                                (FStar_Util.is_some lift1) &&
                                  (let uu____10836 =
                                     let uu____10838 =
                                       let uu____10841 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10841
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10838
                                       FStar_List.length
                                      in
                                   uu____10836 <> Prims.int_one)
                                 in
                              if uu____10833
                              then
                                let uu____10880 =
                                  let uu____10886 =
                                    let uu____10888 =
                                      FStar_Syntax_Print.lid_to_string
                                        sub1.FStar_Syntax_Syntax.source
                                       in
                                    let uu____10890 =
                                      FStar_Syntax_Print.lid_to_string
                                        sub1.FStar_Syntax_Syntax.target
                                       in
                                    let uu____10892 =
                                      let uu____10894 =
                                        let uu____10896 =
                                          let uu____10899 =
                                            FStar_All.pipe_right lift1
                                              FStar_Util.must
                                             in
                                          FStar_All.pipe_right uu____10899
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____10896
                                          FStar_List.length
                                         in
                                      FStar_All.pipe_right uu____10894
                                        FStar_Util.string_of_int
                                       in
                                    FStar_Util.format3
                                      "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                      uu____10888 uu____10890 uu____10892
                                     in
                                  (FStar_Errors.Fatal_TooManyUniverse,
                                    uu____10886)
                                   in
                                FStar_Errors.raise_error uu____10880 r
                              else ());
                             (let sub2 =
                                let uu___1337_10942 = sub1  in
                                {
                                  FStar_Syntax_Syntax.source =
                                    (uu___1337_10942.FStar_Syntax_Syntax.source);
                                  FStar_Syntax_Syntax.target =
                                    (uu___1337_10942.FStar_Syntax_Syntax.target);
                                  FStar_Syntax_Syntax.lift_wp =
                                    (FStar_Pervasives_Native.Some lift_wp);
                                  FStar_Syntax_Syntax.lift = lift1
                                }  in
                              let se1 =
                                let uu___1340_10944 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1340_10944.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1340_10944.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1340_10944.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1340_10944.FStar_Syntax_Syntax.sigattrs)
                                }  in
                              ([se1], [], env0))))))
=======
=======
>>>>>>> snap
           let sub2 = FStar_TypeChecker_TcEffect.tc_lift env sub1 r  in
           let se1 =
             let uu___384_2347 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_sub_effect sub2);
               FStar_Syntax_Syntax.sigrng =
                 (uu___384_2347.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___384_2347.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___384_2347.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___384_2347.FStar_Syntax_Syntax.sigattrs)
             }  in
           ([se1], [], env)
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let uu____2361 =
             FStar_TypeChecker_TcEffect.tc_effect_abbrev env
               (lid, uvs, tps, c) r
              in
           (match uu____2361 with
            | (lid1,uvs1,tps1,c1) ->
                let se1 =
                  let uu___399_2385 = se  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_effect_abbrev
                         (lid1, uvs1, tps1, c1, flags));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___399_2385.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___399_2385.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___399_2385.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___399_2385.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([se1], [], env0))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____2392,uu____2393,uu____2394) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_2399  ->
                   match uu___1_2399 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____2402 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____2408,uu____2409) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_2418  ->
                   match uu___1_2418 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____2421 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____2432 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____2432
             then
               let uu____2435 =
                 let uu____2441 =
                   let uu____2443 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____2443
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____2441)
                  in
               FStar_Errors.raise_error uu____2435 r
             else ());
            (let uu____2449 =
               let uu____2458 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____2458
               then
                 let uu____2469 =
                   tc_declare_typ
                     (let uu___423_2472 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___423_2472.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___423_2472.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___423_2472.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___423_2472.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___423_2472.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___423_2472.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___423_2472.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___423_2472.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___423_2472.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___423_2472.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___423_2472.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___423_2472.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___423_2472.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___423_2472.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___423_2472.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___423_2472.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___423_2472.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___423_2472.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___423_2472.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___423_2472.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___423_2472.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___423_2472.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___423_2472.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___423_2472.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___423_2472.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___423_2472.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___423_2472.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___423_2472.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___423_2472.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___423_2472.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___423_2472.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___423_2472.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___423_2472.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___423_2472.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                          (uu___1460_11547.FStar_TypeChecker_Env.synth_hook);
=======
                          (uu___1458_11629.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.try_solve_implicits_hook =
                          (uu___1458_11629.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                          (uu___1434_11460.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.try_solve_implicits_hook =
                          (uu___1434_11460.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                          (uu___423_2472.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.try_solve_implicits_hook =
                          (uu___423_2472.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                          (uu___423_2472.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.try_solve_implicits_hook =
                          (uu___423_2472.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
                        FStar_TypeChecker_Env.splice =
                          (uu___423_2472.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___423_2472.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___423_2472.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___423_2472.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___423_2472.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___423_2472.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___423_2472.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___423_2472.FStar_TypeChecker_Env.strict_args_tab)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____2469 with
                 | (uvs1,t1) ->
                     ((let uu____2497 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____2497
                       then
                         let uu____2502 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____2504 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____2502 uu____2504
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____2449 with
             | (uvs1,t1) ->
                 let uu____2539 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____2539 with
                  | (uvs2,t2) ->
                      ([(let uu___436_2569 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___436_2569.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___436_2569.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___436_2569.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___436_2569.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____2574 =
             let uu____2583 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____2583
             then
               let uu____2594 =
                 tc_assume
                   (let uu___445_2597 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___445_2597.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___445_2597.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___445_2597.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___445_2597.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___445_2597.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___445_2597.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___445_2597.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___445_2597.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___445_2597.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___445_2597.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___445_2597.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___445_2597.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___445_2597.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___445_2597.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___445_2597.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___445_2597.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___445_2597.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___445_2597.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___445_2597.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___445_2597.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___445_2597.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___445_2597.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___445_2597.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___445_2597.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___445_2597.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___445_2597.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___445_2597.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___445_2597.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___445_2597.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___445_2597.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___445_2597.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___445_2597.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___445_2597.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                        (uu___1482_11672.FStar_TypeChecker_Env.synth_hook);
=======
                        (uu___1480_11754.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1480_11754.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                        (uu___1456_11585.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1456_11585.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                        (uu___445_2597.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___445_2597.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                        (uu___445_2597.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___445_2597.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
                      FStar_TypeChecker_Env.splice =
                        (uu___445_2597.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___445_2597.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___445_2597.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___445_2597.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___445_2597.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___445_2597.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___445_2597.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___445_2597.FStar_TypeChecker_Env.strict_args_tab)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____2594 with
               | (uvs1,t1) ->
                   ((let uu____2623 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____2623
                     then
                       let uu____2628 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____2630 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____2628
                         uu____2630
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____2574 with
            | (uvs1,t1) ->
                let uu____2665 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____2665 with
                 | (uvs2,t2) ->
                     ([(let uu___458_2695 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___458_2695.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___458_2695.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___458_2695.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___458_2695.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____2699 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____2699 with
            | (e1,c,g1) ->
                let uu____2719 =
                  let uu____2726 = FStar_TypeChecker_Common.lcomp_comp c  in
                  match uu____2726 with
                  | (c1,g_lc) ->
                      let uu____2739 =
                        let uu____2746 =
                          let uu____2749 =
                            FStar_Syntax_Util.ml_comp
                              FStar_Syntax_Syntax.t_unit r
                             in
                          FStar_Pervasives_Native.Some uu____2749  in
                        FStar_TypeChecker_TcTerm.check_expected_effect env2
                          uu____2746 (e1, c1)
                         in
                      (match uu____2739 with
                       | (e2,_x,g) ->
                           let uu____2759 =
                             FStar_TypeChecker_Env.conj_guard g_lc g  in
                           (e2, _x, uu____2759))
                   in
                (match uu____2719 with
                 | (e2,uu____2771,g) ->
                     ((let uu____2774 = FStar_TypeChecker_Env.conj_guard g1 g
                          in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____2774);
                      (let se1 =
                         let uu___480_2776 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___480_2776.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___480_2776.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___480_2776.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___480_2776.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____2788 = FStar_Options.debug_any ()  in
             if uu____2788
             then
               let uu____2791 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____2793 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____2791
                 uu____2793
             else ());
            (let uu____2798 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____2798 with
             | (t1,uu____2816,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____2830 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____2830 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____2833 =
                              let uu____2839 =
                                let uu____2841 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____2843 =
                                  let uu____2845 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____2845
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____2841 uu____2843
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____2839)
                               in
                            FStar_Errors.raise_error uu____2833 r
                        | uu____2857 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___501_2862 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___501_2862.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___501_2862.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___501_2862.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___501_2862.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___501_2862.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___501_2862.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___501_2862.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___501_2862.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___501_2862.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___501_2862.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___501_2862.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___501_2862.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___501_2862.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___501_2862.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___501_2862.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___501_2862.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___501_2862.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___501_2862.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___501_2862.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___501_2862.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___501_2862.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___501_2862.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___501_2862.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___501_2862.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___501_2862.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___501_2862.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___501_2862.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___501_2862.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___501_2862.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___501_2862.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___501_2862.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___501_2862.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___501_2862.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___501_2862.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___501_2862.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                          (uu___1538_11937.FStar_TypeChecker_Env.synth_hook);
=======
                          (uu___1536_12019.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.try_solve_implicits_hook =
                          (uu___1536_12019.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                          (uu___1512_11850.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.try_solve_implicits_hook =
                          (uu___1512_11850.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                          (uu___501_2862.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.try_solve_implicits_hook =
                          (uu___501_2862.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                          (uu___501_2862.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.try_solve_implicits_hook =
                          (uu___501_2862.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
                        FStar_TypeChecker_Env.splice =
                          (uu___501_2862.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___501_2862.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___501_2862.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___501_2862.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___501_2862.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___501_2862.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___501_2862.FStar_TypeChecker_Env.strict_args_tab)
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
                 let uu____2930 =
                   let uu____2932 =
                     let uu____2941 = drop_logic val_q  in
                     let uu____2944 = drop_logic q'  in
                     (uu____2941, uu____2944)  in
                   match uu____2932 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____2930
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____2971 =
                      let uu____2977 =
                        let uu____2979 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____2981 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____2983 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____2979 uu____2981 uu____2983
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____2977)
                       in
                    FStar_Errors.raise_error uu____2971 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____3020 =
                   let uu____3021 = FStar_Syntax_Subst.compress def  in
                   uu____3021.FStar_Syntax_Syntax.n  in
                 match uu____3020 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____3033,uu____3034)
                     -> binders
                 | uu____3059 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____3071;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____3176) -> val_bs1
                     | (uu____3207,[]) -> val_bs1
                     | ((body_bv,uu____3239)::bt,(val_bv,aqual)::vt) ->
                         let uu____3296 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____3320) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___570_3334 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___572_3337 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___572_3337.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___570_3334.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___570_3334.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____3296
                      in
                   let uu____3344 =
                     let uu____3351 =
                       let uu____3352 =
                         let uu____3367 = rename_binders1 def_bs val_bs  in
                         (uu____3367, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____3352  in
                     FStar_Syntax_Syntax.mk uu____3351  in
                   uu____3344 FStar_Pervasives_Native.None r1
               | uu____3386 -> typ1  in
             let uu___578_3387 = lb  in
             let uu____3388 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___578_3387.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___578_3387.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____3388;
               FStar_Syntax_Syntax.lbeff =
                 (uu___578_3387.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___578_3387.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___578_3387.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___578_3387.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____3391 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____3446  ->
                     fun lb  ->
                       match uu____3446 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____3492 =
                             let uu____3504 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____3504 with
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
                                   | uu____3584 ->
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
                                  (let uu____3631 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____3631, quals_opt1)))
                              in
                           (match uu____3492 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____3391 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____3735 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___2_3741  ->
                                match uu___2_3741 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____3746 -> false))
                         in
                      if uu____3735
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____3759 =
                    let uu____3766 =
                      let uu____3767 =
                        let uu____3781 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____3781)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____3767  in
                    FStar_Syntax_Syntax.mk uu____3766  in
                  uu____3759 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___621_3800 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___621_3800.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___621_3800.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___621_3800.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___621_3800.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___621_3800.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___621_3800.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___621_3800.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___621_3800.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___621_3800.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___621_3800.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___621_3800.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___621_3800.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___621_3800.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___621_3800.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___621_3800.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___621_3800.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___621_3800.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___621_3800.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___621_3800.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___621_3800.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___621_3800.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___621_3800.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___621_3800.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___621_3800.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___621_3800.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___621_3800.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___621_3800.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___621_3800.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___621_3800.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___621_3800.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___621_3800.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___621_3800.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___621_3800.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                      (uu___1658_12875.FStar_TypeChecker_Env.synth_hook);
=======
                      (uu___1656_12957.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___1656_12957.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                      (uu___1632_12788.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___1632_12788.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                      (uu___621_3800.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___621_3800.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                      (uu___621_3800.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___621_3800.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
                    FStar_TypeChecker_Env.splice =
                      (uu___621_3800.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___621_3800.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___621_3800.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___621_3800.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___621_3800.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___621_3800.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___621_3800.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___621_3800.FStar_TypeChecker_Env.strict_args_tab)
                  }  in
                let e1 =
                  let uu____3803 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____3803
                  then
                    let drop_lbtyp e_lax =
                      let uu____3812 =
                        let uu____3813 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____3813.FStar_Syntax_Syntax.n  in
                      match uu____3812 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____3835 =
                              let uu____3836 = FStar_Syntax_Subst.compress e
                                 in
                              uu____3836.FStar_Syntax_Syntax.n  in
                            match uu____3835 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____3840,lb1::[]),uu____3842) ->
                                let uu____3858 =
                                  let uu____3859 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____3859.FStar_Syntax_Syntax.n  in
                                (match uu____3858 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____3864 -> false)
                            | uu____3866 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___646_3870 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___648_3885 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___648_3885.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___648_3885.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___648_3885.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___648_3885.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___648_3885.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___648_3885.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___646_3870.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___646_3870.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____3888 -> e_lax  in
                    let uu____3889 =
                      FStar_Util.record_time
                        (fun uu____3897  ->
                           let uu____3898 =
                             let uu____3899 =
                               let uu____3900 =
                                 FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                   (let uu___652_3909 = env'  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___652_3909.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___652_3909.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___652_3909.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___652_3909.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___652_3909.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___652_3909.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___652_3909.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___652_3909.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___652_3909.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___652_3909.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___652_3909.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___652_3909.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___652_3909.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___652_3909.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___652_3909.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___652_3909.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___652_3909.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___652_3909.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___652_3909.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___652_3909.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___652_3909.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___652_3909.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___652_3909.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___652_3909.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___652_3909.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___652_3909.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___652_3909.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___652_3909.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___652_3909.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___652_3909.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___652_3909.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___652_3909.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___652_3909.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                        (uu___1689_12984.FStar_TypeChecker_Env.synth_hook);
=======
                                        (uu___1687_13066.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___1687_13066.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                        (uu___1663_12897.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___1663_12897.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
=======
>>>>>>> snap
                                        (uu___652_3909.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___652_3909.FStar_TypeChecker_Env.try_solve_implicits_hook);
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
                                      FStar_TypeChecker_Env.splice =
                                        (uu___652_3909.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___652_3909.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___652_3909.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___652_3909.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___652_3909.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___652_3909.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___652_3909.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___652_3909.FStar_TypeChecker_Env.strict_args_tab)
                                    }) e
                                  in
                               FStar_All.pipe_right uu____3900
                                 (fun uu____3922  ->
                                    match uu____3922 with
                                    | (e1,uu____3930,uu____3931) -> e1)
                                in
                             FStar_All.pipe_right uu____3899
                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                  env')
                              in
                           FStar_All.pipe_right uu____3898 drop_lbtyp)
                       in
                    match uu____3889 with
                    | (e1,ms) ->
                        ((let uu____3937 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TwoPhases")
                             in
                          if uu____3937
                          then
                            let uu____3942 =
                              FStar_Syntax_Print.term_to_string e1  in
                            FStar_Util.print1
                              "Let binding after phase 1: %s\n" uu____3942
                          else ());
                         (let uu____3948 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TCDeclTime")
                             in
                          if uu____3948
                          then
                            let uu____3953 = FStar_Util.string_of_int ms  in
                            FStar_Util.print1
                              "Let binding elaborated (phase 1) in %s milliseconds\n"
                              uu____3953
                          else ());
                         e1)
                  else e  in
                let uu____3960 =
                  let uu____3969 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____3969 with
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
                (match uu____3960 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___682_4074 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___682_4074.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___682_4074.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___682_4074.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___682_4074.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___689_4087 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___689_4087.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___689_4087.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___689_4087.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___689_4087.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___689_4087.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___689_4087.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____4088 =
                       FStar_Util.record_time
                         (fun uu____4107  ->
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              env' e1)
                        in
                     (match uu____4088 with
                      | (r1,ms) ->
                          ((let uu____4135 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TCDeclTime")
                               in
                            if uu____4135
                            then
                              let uu____4140 = FStar_Util.string_of_int ms
                                 in
                              FStar_Util.print1
                                "Let binding typechecked in phase 2 in %s milliseconds\n"
                                uu____4140
                            else ());
                           (let uu____4145 =
                              match r1 with
                              | ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                                   FStar_Syntax_Syntax.pos = uu____4170;
                                   FStar_Syntax_Syntax.vars = uu____4171;_},uu____4172,g)
                                  when FStar_TypeChecker_Env.is_trivial g ->
                                  let lbs2 =
                                    let uu____4202 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.snd lbs1)
                                        (FStar_List.map rename_parameters)
                                       in
                                    ((FStar_Pervasives_Native.fst lbs1),
                                      uu____4202)
                                     in
                                  let lbs3 =
                                    let uu____4226 =
                                      match post_tau with
                                      | FStar_Pervasives_Native.Some tau ->
                                          FStar_List.map (postprocess_lb tau)
                                            (FStar_Pervasives_Native.snd lbs2)
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.snd lbs2
                                       in
                                    ((FStar_Pervasives_Native.fst lbs2),
                                      uu____4226)
                                     in
                                  let quals1 =
                                    match e2.FStar_Syntax_Syntax.n with
                                    | FStar_Syntax_Syntax.Tm_meta
                                        (uu____4249,FStar_Syntax_Syntax.Meta_desugared
                                         (FStar_Syntax_Syntax.Masked_effect
                                         ))
                                        ->
                                        FStar_Syntax_Syntax.HasMaskedEffect
                                        :: quals
                                    | uu____4254 -> quals  in
                                  ((let uu___719_4263 = se1  in
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_let
                                           (lbs3, lids));
                                      FStar_Syntax_Syntax.sigrng =
                                        (uu___719_4263.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals = quals1;
                                      FStar_Syntax_Syntax.sigmeta =
                                        (uu___719_4263.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (uu___719_4263.FStar_Syntax_Syntax.sigattrs)
                                    }), lbs3)
                              | uu____4266 ->
                                  failwith
                                    "impossible (typechecking should preserve Tm_let)"
                               in
                            match uu____4145 with
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
                                 (let uu____4322 = log env1  in
                                  if uu____4322
                                  then
                                    let uu____4325 =
                                      let uu____4327 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.snd lbs1)
                                          (FStar_List.map
                                             (fun lb  ->
                                                let should_log =
                                                  let uu____4347 =
                                                    let uu____4356 =
                                                      let uu____4357 =
                                                        let uu____4360 =
                                                          FStar_Util.right
                                                            lb.FStar_Syntax_Syntax.lbname
                                                           in
                                                        uu____4360.FStar_Syntax_Syntax.fv_name
                                                         in
                                                      uu____4357.FStar_Syntax_Syntax.v
                                                       in
                                                    FStar_TypeChecker_Env.try_lookup_val_decl
                                                      env1 uu____4356
                                                     in
                                                  match uu____4347 with
                                                  | FStar_Pervasives_Native.None
                                                       -> true
                                                  | uu____4369 -> false  in
                                                if should_log
                                                then
                                                  let uu____4381 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  let uu____4383 =
                                                    FStar_Syntax_Print.term_to_string
                                                      lb.FStar_Syntax_Syntax.lbtyp
                                                     in
                                                  FStar_Util.format2
                                                    "let %s : %s" uu____4381
                                                    uu____4383
                                                else ""))
                                         in
                                      FStar_All.pipe_right uu____4327
                                        (FStar_String.concat "\n")
                                       in
                                    FStar_Util.print1 "%s\n" uu____4325
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
      (let uu____4435 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____4435
       then
         let uu____4438 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____4438
       else ());
      (let uu____4443 = get_fail_se se  in
       match uu____4443 with
       | FStar_Pervasives_Native.Some (uu____4464,false ) when
           let uu____4481 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____4481 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___750_4507 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___750_4507.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___750_4507.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___750_4507.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___750_4507.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___750_4507.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___750_4507.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___750_4507.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___750_4507.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___750_4507.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___750_4507.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___750_4507.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___750_4507.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___750_4507.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___750_4507.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___750_4507.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___750_4507.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___750_4507.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___750_4507.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___750_4507.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___750_4507.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___750_4507.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___750_4507.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___750_4507.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___750_4507.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___750_4507.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___750_4507.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___750_4507.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___750_4507.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___750_4507.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___750_4507.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___750_4507.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___750_4507.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___750_4507.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___750_4507.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                   (uu___1787_13582.FStar_TypeChecker_Env.synth_hook);
=======
                   (uu___1785_13664.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.try_solve_implicits_hook =
                   (uu___1785_13664.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                   (uu___1761_13495.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.try_solve_implicits_hook =
                   (uu___1761_13495.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                   (uu___750_4507.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.try_solve_implicits_hook =
                   (uu___750_4507.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                   (uu___750_4507.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.try_solve_implicits_hook =
                   (uu___750_4507.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
                 FStar_TypeChecker_Env.splice =
                   (uu___750_4507.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___750_4507.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___750_4507.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___750_4507.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___750_4507.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___750_4507.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___750_4507.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___750_4507.FStar_TypeChecker_Env.strict_args_tab)
               }
             else env1  in
           ((let uu____4512 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____4512
             then
               let uu____4515 =
                 let uu____4517 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____4517
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____4515
             else ());
            (let uu____4531 =
               FStar_Errors.catch_errors
                 (fun uu____4561  ->
                    FStar_Options.with_saved_options
                      (fun uu____4573  -> tc_decl' env' se))
                in
             match uu____4531 with
             | (errs,uu____4585) ->
                 ((let uu____4615 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____4615
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____4650 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____4650  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____4662 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____4673 =
                            let uu____4683 = check_multi_eq errnos1 actual
                               in
                            match uu____4683 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- Prims.int_one), (~- Prims.int_one),
                                  (~- Prims.int_one))
                             in
                          (match uu____4673 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____4748 =
                                   let uu____4754 =
                                     let uu____4756 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____4759 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____4762 =
                                       FStar_Util.string_of_int e  in
                                     let uu____4764 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____4766 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____4756 uu____4759 uu____4762
                                       uu____4764 uu____4766
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____4754)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____4748)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____4793 .
    'Auu____4793 ->
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
               (fun uu___3_4836  ->
                  match uu___3_4836 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____4839 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____4850) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____4858 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____4868 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____4873 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____4889 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____4915 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4941) ->
            let uu____4950 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____4950
            then
              let for_export_bundle se1 uu____4987 =
                match uu____4987 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____5026,uu____5027) ->
                         let dec =
                           let uu___826_5037 = se1  in
                           let uu____5038 =
                             let uu____5039 =
                               let uu____5046 =
                                 let uu____5047 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____5047  in
                               (l, us, uu____5046)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____5039
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____5038;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___826_5037.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___826_5037.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___826_5037.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____5057,uu____5058,uu____5059) ->
                         let dec =
                           let uu___837_5067 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___837_5067.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___837_5067.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___837_5067.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____5072 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume (uu____5095,uu____5096,uu____5097)
            ->
            let uu____5098 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____5098 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____5122 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____5122
            then
              ([(let uu___853_5141 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___853_5141.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___853_5141.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___853_5141.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____5144 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_5150  ->
                         match uu___4_5150 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____5153 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____5159 ->
                             true
                         | uu____5161 -> false))
                  in
               if uu____5144 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____5182 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____5187 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5192 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____5197 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____5202 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____5220) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____5234 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____5234
            then ([], hidden)
            else
              (let dec =
                 let uu____5255 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____5255;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____5266 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____5266
            then
              let uu____5277 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___890_5291 = se  in
                        let uu____5292 =
                          let uu____5293 =
                            let uu____5300 =
                              let uu____5301 =
                                let uu____5304 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____5304.FStar_Syntax_Syntax.fv_name  in
                              uu____5301.FStar_Syntax_Syntax.v  in
                            (uu____5300, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____5293  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____5292;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___890_5291.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___890_5291.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___890_5291.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____5277, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> Prims.bool -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
<<<<<<< HEAD
      (let uu____5327 = FStar_TypeChecker_Env.debug env FStar_Options.Low  in
       if uu____5327
       then
         let uu____5330 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____5330
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____5335 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____5353 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
           uu____5370) ->
           let env1 =
             let uu___911_5375 = env  in
             let uu____5376 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___911_5375.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___911_5375.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___911_5375.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___911_5375.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___911_5375.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___911_5375.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___911_5375.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___911_5375.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___911_5375.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___911_5375.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___911_5375.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___911_5375.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___911_5375.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___911_5375.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___911_5375.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___911_5375.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___911_5375.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___911_5375.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___911_5375.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___911_5375.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___911_5375.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___911_5375.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___911_5375.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___911_5375.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___911_5375.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___911_5375.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___911_5375.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___911_5375.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___911_5375.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___911_5375.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___911_5375.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___911_5375.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___911_5375.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___911_5375.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____5376;
               FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                 (uu___1948_14450.FStar_TypeChecker_Env.synth_hook);
=======
                 (uu___1946_14532.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___1946_14532.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                 (uu___1922_14363.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___1922_14363.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                 (uu___911_5375.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___911_5375.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
               FStar_TypeChecker_Env.splice =
                 (uu___911_5375.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___911_5375.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___911_5375.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___911_5375.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___911_5375.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___911_5375.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___911_5375.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___911_5375.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
           let env1 =
             let uu___911_5378 = env  in
             let uu____5379 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___911_5378.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___911_5378.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___911_5378.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___911_5378.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___911_5378.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___911_5378.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___911_5378.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___911_5378.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___911_5378.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___911_5378.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___911_5378.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___911_5378.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___911_5378.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___911_5378.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___911_5378.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___911_5378.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___911_5378.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___911_5378.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___911_5378.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___911_5378.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___911_5378.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___911_5378.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___911_5378.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___911_5378.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___911_5378.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___911_5378.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___911_5378.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___911_5378.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___911_5378.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___911_5378.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___911_5378.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___911_5378.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___911_5378.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___911_5378.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____5379;
               FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                 (uu___1948_14453.FStar_TypeChecker_Env.synth_hook);
=======
                 (uu___1946_14535.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___1946_14535.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                 (uu___1922_14366.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___1922_14366.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                 (uu___911_5378.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___911_5378.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
               FStar_TypeChecker_Env.splice =
                 (uu___911_5378.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___911_5378.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___911_5378.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___911_5378.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___911_5378.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___911_5378.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___911_5378.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___911_5378.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions
           uu____5380) ->
           let env1 =
             let uu___911_5383 = env  in
             let uu____5384 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___911_5383.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___911_5383.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___911_5383.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___911_5383.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___911_5383.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___911_5383.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___911_5383.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___911_5383.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___911_5383.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___911_5383.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___911_5383.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___911_5383.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___911_5383.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___911_5383.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___911_5383.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___911_5383.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___911_5383.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___911_5383.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___911_5383.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___911_5383.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___911_5383.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___911_5383.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___911_5383.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___911_5383.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___911_5383.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___911_5383.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___911_5383.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___911_5383.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___911_5383.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___911_5383.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___911_5383.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___911_5383.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___911_5383.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___911_5383.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____5384;
               FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                 (uu___1948_14458.FStar_TypeChecker_Env.synth_hook);
=======
                 (uu___1946_14540.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___1946_14540.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                 (uu___1922_14371.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___1922_14371.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                 (uu___911_5383.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___911_5383.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
               FStar_TypeChecker_Env.splice =
                 (uu___911_5383.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___911_5383.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___911_5383.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___911_5383.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___911_5383.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___911_5383.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___911_5383.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___911_5383.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____5385) ->
           let env1 =
             let uu___911_5390 = env  in
             let uu____5391 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___911_5390.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___911_5390.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___911_5390.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___911_5390.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___911_5390.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___911_5390.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___911_5390.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___911_5390.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___911_5390.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___911_5390.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___911_5390.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___911_5390.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___911_5390.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___911_5390.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___911_5390.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___911_5390.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___911_5390.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___911_5390.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___911_5390.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___911_5390.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___911_5390.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___911_5390.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___911_5390.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___911_5390.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___911_5390.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___911_5390.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___911_5390.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___911_5390.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___911_5390.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___911_5390.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___911_5390.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___911_5390.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___911_5390.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___911_5390.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____5391;
               FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                 (uu___1948_14465.FStar_TypeChecker_Env.synth_hook);
=======
                 (uu___1946_14547.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___1946_14547.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                 (uu___1922_14378.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___1922_14378.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                 (uu___911_5390.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___911_5390.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
               FStar_TypeChecker_Env.splice =
                 (uu___911_5390.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___911_5390.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___911_5390.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___911_5390.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___911_5390.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___911_5390.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___911_5390.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___911_5390.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver )
           ->
           ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
              ();
            env)
       | FStar_Syntax_Syntax.Sig_pragma uu____5393 -> env
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5394 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____5404 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____5404) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5405,uu____5406,uu____5407) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_5412  ->
                   match uu___5_5412 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5415 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____5417,uu____5418) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_5427  ->
                   match uu___5_5427 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5430 -> false))
           -> env
       | uu____5432 -> FStar_TypeChecker_Env.push_sigelt env se)
=======
      fun from_cache  ->
        (let uu____5334 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____5334
         then
           let uu____5337 = FStar_Syntax_Print.sigelt_to_string se  in
           let uu____5339 = FStar_Util.string_of_bool from_cache  in
           FStar_Util.print2
             ">>>>>>>>>>>>>>Adding top-level decl to environment: %s (from_cache:%s)\n"
             uu____5337 uu____5339
         else ());
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____5344 ->
             let uu____5361 =
               let uu____5367 =
                 let uu____5369 = FStar_Syntax_Print.sigelt_to_string se  in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____5369
                  in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____5367)  in
             FStar_Errors.raise_error uu____5361
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_datacon uu____5373 ->
             let uu____5389 =
               let uu____5395 =
                 let uu____5397 = FStar_Syntax_Print.sigelt_to_string se  in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____5397
                  in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____5395)  in
             FStar_Errors.raise_error uu____5389
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_declare_typ
             (uu____5401,uu____5402,uu____5403) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___5_5408  ->
                     match uu___5_5408 with
                     | FStar_Syntax_Syntax.OnlyName  -> true
                     | uu____5411 -> false))
             -> env
         | FStar_Syntax_Syntax.Sig_let (uu____5413,uu____5414) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___5_5423  ->
                     match uu___5_5423 with
                     | FStar_Syntax_Syntax.OnlyName  -> true
                     | uu____5426 -> false))
             -> env
         | uu____5428 ->
             let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PushOptions uu____5430) ->
                  if from_cache
                  then env1
                  else
                    (let uu___927_5437 = env1  in
                     let uu____5438 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___927_5437.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___927_5437.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___927_5437.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___927_5437.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___927_5437.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___927_5437.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___927_5437.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___927_5437.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___927_5437.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___927_5437.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___927_5437.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___927_5437.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___927_5437.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___927_5437.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___927_5437.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___927_5437.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___927_5437.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___927_5437.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___927_5437.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___927_5437.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___927_5437.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___927_5437.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___927_5437.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___927_5437.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___927_5437.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___927_5437.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___927_5437.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___927_5437.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___927_5437.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___927_5437.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___927_5437.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___927_5437.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___927_5437.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___927_5437.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5438;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___927_5437.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___927_5437.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___927_5437.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___927_5437.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___927_5437.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___927_5437.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___927_5437.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___927_5437.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___927_5437.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___927_5437.FStar_TypeChecker_Env.strict_args_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PopOptions ) ->
                  if from_cache
                  then env1
                  else
                    (let uu___927_5442 = env1  in
                     let uu____5443 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___927_5442.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___927_5442.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___927_5442.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___927_5442.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___927_5442.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___927_5442.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___927_5442.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___927_5442.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___927_5442.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___927_5442.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___927_5442.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___927_5442.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___927_5442.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___927_5442.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___927_5442.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___927_5442.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___927_5442.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___927_5442.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___927_5442.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___927_5442.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___927_5442.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___927_5442.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___927_5442.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___927_5442.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___927_5442.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___927_5442.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___927_5442.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___927_5442.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___927_5442.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___927_5442.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___927_5442.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___927_5442.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___927_5442.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___927_5442.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5443;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___927_5442.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___927_5442.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___927_5442.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___927_5442.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___927_5442.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___927_5442.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___927_5442.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___927_5442.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___927_5442.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___927_5442.FStar_TypeChecker_Env.strict_args_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.SetOptions uu____5444) ->
                  if from_cache
                  then env1
                  else
                    (let uu___927_5449 = env1  in
                     let uu____5450 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___927_5449.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___927_5449.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___927_5449.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___927_5449.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___927_5449.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___927_5449.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___927_5449.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___927_5449.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___927_5449.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___927_5449.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___927_5449.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___927_5449.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___927_5449.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___927_5449.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___927_5449.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___927_5449.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___927_5449.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___927_5449.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___927_5449.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___927_5449.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___927_5449.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___927_5449.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___927_5449.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___927_5449.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___927_5449.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___927_5449.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___927_5449.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___927_5449.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___927_5449.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___927_5449.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___927_5449.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___927_5449.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___927_5449.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___927_5449.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5450;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___927_5449.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___927_5449.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___927_5449.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___927_5449.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___927_5449.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___927_5449.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___927_5449.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___927_5449.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___927_5449.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___927_5449.FStar_TypeChecker_Env.strict_args_tab)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.ResetOptions uu____5451) ->
                  if from_cache
                  then env1
                  else
                    (let uu___927_5458 = env1  in
                     let uu____5459 = FStar_Options.using_facts_from ()  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___927_5458.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___927_5458.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___927_5458.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___927_5458.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___927_5458.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___927_5458.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___927_5458.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___927_5458.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___927_5458.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___927_5458.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___927_5458.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___927_5458.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___927_5458.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___927_5458.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___927_5458.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___927_5458.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___927_5458.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___927_5458.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___927_5458.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___927_5458.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___927_5458.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___927_5458.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___927_5458.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___927_5458.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___927_5458.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___927_5458.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___927_5458.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___927_5458.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___927_5458.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___927_5458.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___927_5458.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___927_5458.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___927_5458.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___927_5458.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____5459;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___927_5458.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___927_5458.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___927_5458.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___927_5458.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___927_5458.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___927_5458.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___927_5458.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___927_5458.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___927_5458.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___927_5458.FStar_TypeChecker_Env.strict_args_tab)
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
                            let uu____5475 =
                              FStar_Syntax_Util.action_as_lb
                                ne.FStar_Syntax_Syntax.mname a
                                (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Env.push_sigelt env3 uu____5475)
                       env2)
              | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
<<<<<<< HEAD
                  FStar_TypeChecker_Env.update_effect_lattice env1 sub1
              | uu____13566 -> env1))
>>>>>>> snap
=======
                  let sub_or_lift_t =
                    let uu____5484 =
                      (FStar_TypeChecker_Env.is_layered_effect env1
                         sub1.FStar_Syntax_Syntax.source)
                        ||
                        (FStar_TypeChecker_Env.is_layered_effect env1
                           sub1.FStar_Syntax_Syntax.target)
                       in
                    if uu____5484
                    then
                      let uu____5493 =
                        let uu____5498 =
                          FStar_All.pipe_right
                            sub1.FStar_Syntax_Syntax.lift_wp FStar_Util.must
                           in
                        FStar_TypeChecker_Util.lift_tf_layered_effect
                          sub1.FStar_Syntax_Syntax.target uu____5498
                         in
                      FStar_Util.Inr uu____5493
                    else FStar_Util.Inl sub1  in
                  FStar_TypeChecker_Env.update_effect_lattice env1
                    sub1.FStar_Syntax_Syntax.source
                    sub1.FStar_Syntax_Syntax.target sub_or_lift_t
              | uu____5507 -> env1))
>>>>>>> snap
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
<<<<<<< HEAD
<<<<<<< HEAD
      let rec process_one_decl uu____5501 se =
        match uu____5501 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____5554 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____5554
              then
                let uu____5557 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____5557
              else ());
             (let uu____5562 = tc_decl env1 se  in
              match uu____5562 with
=======
      let rec process_one_decl uu____13635 se =
        match uu____13635 with
=======
      let rec process_one_decl uu____5576 se =
        match uu____5576 with
>>>>>>> snap
        | (ses1,exports,env1,hidden) ->
            ((let uu____5629 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____5629
              then
                let uu____5632 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____5632
              else ());
<<<<<<< HEAD
             (let uu____13696 = tc_decl env1 se  in
              match uu____13696 with
>>>>>>> snap
=======
             (let uu____5637 = tc_decl env1 se  in
              match uu____5637 with
>>>>>>> snap
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
<<<<<<< HEAD
<<<<<<< HEAD
                            (let uu____5615 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____5615
                             then
                               let uu____5619 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____5619
=======
                            (let uu____13749 =
=======
                            (let uu____5690 =
>>>>>>> snap
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____5690
                             then
                               let uu____5694 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
<<<<<<< HEAD
                                 "About to elim vars from %s\n" uu____13753
>>>>>>> snap
=======
                                 "About to elim vars from %s\n" uu____5694
>>>>>>> snap
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
<<<<<<< HEAD
<<<<<<< HEAD
                            (let uu____5635 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____5635
                             then
                               let uu____5639 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____5639
=======
                            (let uu____13769 =
=======
                            (let uu____5710 =
>>>>>>> snap
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____5710
                             then
                               let uu____5714 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
<<<<<<< HEAD
                                 uu____13773
>>>>>>> snap
=======
                                 uu____5714
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
                    (let uu____5656 =
=======
                    (let uu____13791 =
>>>>>>> snap
=======
                    (let uu____5732 =
>>>>>>> snap
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
<<<<<<< HEAD
<<<<<<< HEAD
                     if uu____5656
                     then
                       let uu____5661 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____5670 =
                                  let uu____5672 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____5672 "\n"  in
                                Prims.op_Hat s uu____5670) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____5661
=======
                     if uu____13791
=======
                     if uu____5732
>>>>>>> snap
                     then
                       let uu____5737 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____5746 =
                                  let uu____5748 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____5748 "\n"  in
                                Prims.op_Hat s uu____5746) "" ses'1
                          in
<<<<<<< HEAD
                       FStar_Util.print1 "Checked: %s\n" uu____13796
>>>>>>> snap
=======
                       FStar_Util.print1 "Checked: %s\n" uu____5737
>>>>>>> snap
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
<<<<<<< HEAD
<<<<<<< HEAD
                    (let uu____5682 =
                       let uu____5691 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____5691
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____5733 se1 =
                            match uu____5733 with
                            | (exports1,hidden1) ->
                                let uu____5761 = for_export env3 hidden1 se1
                                   in
                                (match uu____5761 with
=======
                    (let uu____13817 =
                       let uu____13826 =
=======
                    (let uu____5758 =
                       let uu____5767 =
>>>>>>> snap
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____5767
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____5809 se1 =
                            match uu____5809 with
                            | (exports1,hidden1) ->
                                let uu____5837 = for_export env3 hidden1 se1
                                   in
<<<<<<< HEAD
                                (match uu____13896 with
>>>>>>> snap
=======
                                (match uu____5837 with
>>>>>>> snap
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
<<<<<<< HEAD
<<<<<<< HEAD
                     match uu____5682 with
=======
                     match uu____13817 with
>>>>>>> snap
=======
                     match uu____5758 with
>>>>>>> snap
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____5915 = acc  in
        match uu____5915 with
        | (uu____5950,uu____5951,env1,uu____5953) ->
            let r =
              let uu____5987 =
                let uu____5991 =
                  let uu____5993 = FStar_TypeChecker_Env.current_module env1
                     in
                  FStar_Ident.string_of_lid uu____5993  in
                FStar_Pervasives_Native.Some uu____5991  in
              FStar_Profiling.profile
                (fun uu____6016  -> process_one_decl acc se) uu____5987
                "FStar.TypeChecker.Tc.process_one_decl"
               in
            ((let uu____6019 = FStar_Options.profile_group_by_decls ()  in
              if uu____6019
              then
                let tag =
                  match FStar_Syntax_Util.lids_of_sigelt se with
                  | hd1::uu____6026 -> FStar_Ident.string_of_lid hd1
                  | uu____6029 ->
=======
        let uu____14050 = acc  in
        match uu____14050 with
        | (uu____14085,uu____14086,env1,uu____14088) ->
=======
        let uu____5991 = acc  in
        match uu____5991 with
        | (uu____6026,uu____6027,env1,uu____6029) ->
>>>>>>> snap
            let r =
              let uu____6063 =
                let uu____6067 =
                  let uu____6069 = FStar_TypeChecker_Env.current_module env1
                     in
                  FStar_Ident.string_of_lid uu____6069  in
                FStar_Pervasives_Native.Some uu____6067  in
              FStar_Profiling.profile
                (fun uu____6092  -> process_one_decl acc se) uu____6063
                "FStar.TypeChecker.Tc.process_one_decl"
               in
            ((let uu____6095 = FStar_Options.profile_group_by_decls ()  in
              if uu____6095
              then
                let tag =
                  match FStar_Syntax_Util.lids_of_sigelt se with
<<<<<<< HEAD
                  | hd1::uu____14161 -> FStar_Ident.string_of_lid hd1
                  | uu____14164 ->
>>>>>>> snap
=======
                  | hd1::uu____6102 -> FStar_Ident.string_of_lid hd1
                  | uu____6105 ->
>>>>>>> snap
                      FStar_Range.string_of_range
                        (FStar_Syntax_Util.range_of_sigelt se)
                   in
                FStar_Profiling.report_and_clear tag
              else ());
             r)
         in
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____6034 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____6034 with
      | (ses1,exports,env1,uu____6082) ->
=======
      let uu____14169 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____14169 with
      | (ses1,exports,env1,uu____14217) ->
>>>>>>> snap
=======
      let uu____6110 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____6110 with
      | (ses1,exports,env1,uu____6158) ->
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
          let uu___1011_6120 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1011_6120.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1011_6120.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1011_6120.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1011_6120.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1011_6120.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1011_6120.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1011_6120.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1011_6120.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1011_6120.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1011_6120.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___1011_6120.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1011_6120.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1011_6120.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1011_6120.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1011_6120.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___1011_6120.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1011_6120.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___1011_6120.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1011_6120.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___1011_6120.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1011_6120.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1011_6120.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1011_6120.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1011_6120.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1011_6120.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1011_6120.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1011_6120.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1011_6120.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1011_6120.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1011_6120.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1011_6120.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1011_6120.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
              (uu___2048_15195.FStar_TypeChecker_Env.synth_hook);
=======
              (uu___2046_15277.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___2046_15277.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
              (uu___2022_15108.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___2022_15108.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
              (uu___1011_6120.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1011_6120.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
            FStar_TypeChecker_Env.splice =
              (uu___1011_6120.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___1011_6120.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___1011_6120.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1011_6120.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1011_6120.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1011_6120.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1011_6120.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1011_6120.FStar_TypeChecker_Env.strict_args_tab)
          }  in
        let check_term lid univs1 t =
          let uu____6140 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____6140 with
          | (univs2,t1) ->
              ((let uu____6148 =
                  let uu____6150 =
                    let uu____6156 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____6156  in
                  FStar_All.pipe_left uu____6150
                    (FStar_Options.Other "Exports")
                   in
                if uu____6148
                then
                  let uu____6160 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____6162 =
                    let uu____6164 =
=======
          let uu___1850_14255 = env  in
=======
          let uu___1015_6196 = env  in
>>>>>>> snap
          {
            FStar_TypeChecker_Env.solver =
              (uu___1015_6196.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1015_6196.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1015_6196.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1015_6196.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1015_6196.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1015_6196.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1015_6196.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1015_6196.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1015_6196.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1015_6196.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___1015_6196.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1015_6196.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1015_6196.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1015_6196.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1015_6196.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___1015_6196.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1015_6196.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___1015_6196.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1015_6196.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___1015_6196.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1015_6196.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1015_6196.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1015_6196.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1015_6196.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1015_6196.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1015_6196.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1015_6196.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1015_6196.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1015_6196.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1015_6196.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1015_6196.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1015_6196.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1015_6196.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1015_6196.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1015_6196.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___1015_6196.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___1015_6196.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1015_6196.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1015_6196.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1015_6196.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1015_6196.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1015_6196.FStar_TypeChecker_Env.strict_args_tab)
          }  in
        let check_term lid univs1 t =
          let uu____6216 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____6216 with
          | (univs2,t1) ->
              ((let uu____6224 =
                  let uu____6226 =
                    let uu____6232 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____6232  in
                  FStar_All.pipe_left uu____6226
                    (FStar_Options.Other "Exports")
                   in
                if uu____6224
                then
<<<<<<< HEAD
                  let uu____14295 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____14297 =
                    let uu____14299 =
>>>>>>> snap
=======
                  let uu____6236 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____6238 =
                    let uu____6240 =
>>>>>>> snap
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
<<<<<<< HEAD
<<<<<<< HEAD
                    FStar_All.pipe_right uu____6164
                      (FStar_String.concat ", ")
                     in
                  let uu____6181 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____6160 uu____6162 uu____6181
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____6187 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____6187 (fun a1  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____6213 =
             let uu____6215 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____6217 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____6215 uu____6217
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____6213);
=======
                    FStar_All.pipe_right uu____14299
=======
                    FStar_All.pipe_right uu____6240
>>>>>>> snap
                      (FStar_String.concat ", ")
                     in
                  let uu____6257 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____6236 uu____6238 uu____6257
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____6263 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____6263 (fun a1  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____6289 =
             let uu____6291 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____6293 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____6291 uu____6293
              in
<<<<<<< HEAD
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____14348);
>>>>>>> snap
=======
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____6289);
>>>>>>> snap
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
<<<<<<< HEAD
<<<<<<< HEAD
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6228) ->
              let uu____6237 =
                let uu____6239 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6239  in
              if uu____6237
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____6253,uu____6254) ->
              let t =
                let uu____6266 =
                  let uu____6273 =
                    let uu____6274 =
                      let uu____6289 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____6289)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____6274  in
                  FStar_Syntax_Syntax.mk uu____6273  in
                uu____6266 FStar_Pervasives_Native.None
=======
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14363) ->
              let uu____14372 =
                let uu____14374 =
=======
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6304) ->
              let uu____6313 =
                let uu____6315 =
>>>>>>> snap
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6315  in
              if uu____6313
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____6329,uu____6330) ->
              let t =
<<<<<<< HEAD
                let uu____14401 =
                  let uu____14408 =
                    let uu____14409 =
                      let uu____14424 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____14424)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____14409  in
                  FStar_Syntax_Syntax.mk uu____14408  in
                uu____14401 FStar_Pervasives_Native.None
>>>>>>> snap
=======
                let uu____6342 =
                  let uu____6349 =
                    let uu____6350 =
                      let uu____6365 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____6365)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____6350  in
                  FStar_Syntax_Syntax.mk uu____6349  in
                uu____6342 FStar_Pervasives_Native.None
>>>>>>> snap
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
<<<<<<< HEAD
<<<<<<< HEAD
              (l,univs1,t,uu____6305,uu____6306,uu____6307) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____6317 =
                let uu____6319 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6319  in
              if uu____6317 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____6327,lbs),uu____6329) ->
              let uu____6340 =
                let uu____6342 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6342  in
              if uu____6340
=======
              (l,univs1,t,uu____14440,uu____14441,uu____14442) ->
=======
              (l,univs1,t,uu____6381,uu____6382,uu____6383) ->
>>>>>>> snap
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____6393 =
                let uu____6395 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6395  in
              if uu____6393 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____6403,lbs),uu____6405) ->
              let uu____6416 =
                let uu____6418 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
<<<<<<< HEAD
                Prims.op_Negation uu____14477  in
              if uu____14475
>>>>>>> snap
=======
                Prims.op_Negation uu____6418  in
              if uu____6416
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
              let uu____6365 =
                let uu____6367 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6367  in
              if uu____6365
=======
              let uu____14500 =
                let uu____14502 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14502  in
              if uu____14500
>>>>>>> snap
=======
              let uu____6441 =
                let uu____6443 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____6443  in
              if uu____6441
>>>>>>> snap
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
<<<<<<< HEAD
<<<<<<< HEAD
          | FStar_Syntax_Syntax.Sig_main uu____6388 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____6389 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____6396 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____6397 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____6398 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____6399 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____6406 -> ()  in
        let uu____6407 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____6407 then () else FStar_List.iter check_sigelt exports
=======
          | FStar_Syntax_Syntax.Sig_main uu____14523 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____14524 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14531 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14532 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____14533 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____14534 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____14541 -> ()  in
        let uu____14542 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____14542 then () else FStar_List.iter check_sigelt exports
>>>>>>> snap
=======
          | FStar_Syntax_Syntax.Sig_main uu____6464 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____6465 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____6472 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____6473 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____6474 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____6475 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____6482 -> ()  in
        let uu____6483 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____6483 then () else FStar_List.iter check_sigelt exports
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
             | FStar_Syntax_Syntax.Projector (l,uu____6513) -> true
             | uu____6515 -> false) quals
=======
             | FStar_Syntax_Syntax.Projector (l,uu____14648) -> true
             | uu____14650 -> false) quals
>>>>>>> snap
=======
             | FStar_Syntax_Syntax.Projector (l,uu____6589) -> true
             | uu____6591 -> false) quals
>>>>>>> snap
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
<<<<<<< HEAD
<<<<<<< HEAD
          | uu____6545 ->
=======
          | uu____14680 ->
>>>>>>> snap
=======
          | uu____6621 ->
>>>>>>> snap
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
<<<<<<< HEAD
<<<<<<< HEAD
               | uu____6584 ->
                   let uu____6585 =
                     let uu____6592 =
                       let uu____6593 =
                         let uu____6608 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____6608)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____6593  in
                     FStar_Syntax_Syntax.mk uu____6592  in
                   uu____6585 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____6625,uu____6626) ->
            let s1 =
              let uu___1137_6636 = s  in
              let uu____6637 =
                let uu____6638 =
                  let uu____6645 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____6645)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____6638  in
              let uu____6646 =
                let uu____6649 =
                  let uu____6652 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____6652  in
                FStar_Syntax_Syntax.Assumption :: uu____6649  in
              {
                FStar_Syntax_Syntax.sigel = uu____6637;
                FStar_Syntax_Syntax.sigrng =
                  (uu___1137_6636.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____6646;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___1137_6636.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___1137_6636.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____6655 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____6680 lbdef =
        match uu____6680 with
        | (uvs,t) ->
            let attrs =
              let uu____6691 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____6691
              then
                let uu____6696 =
                  let uu____6697 =
=======
               | uu____14719 ->
                   let uu____14720 =
                     let uu____14727 =
                       let uu____14728 =
                         let uu____14743 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____14743)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____14728  in
                     FStar_Syntax_Syntax.mk uu____14727  in
                   uu____14720 FStar_Pervasives_Native.None r)
=======
               | uu____6660 ->
                   let uu____6661 =
                     let uu____6668 =
                       let uu____6669 =
                         let uu____6684 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____6684)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____6669  in
                     FStar_Syntax_Syntax.mk uu____6668  in
                   uu____6661 FStar_Pervasives_Native.None r)
>>>>>>> snap
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____6701,uu____6702) ->
            let s1 =
              let uu___1141_6712 = s  in
              let uu____6713 =
                let uu____6714 =
                  let uu____6721 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____6721)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____6714  in
              let uu____6722 =
                let uu____6725 =
                  let uu____6728 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____6728  in
                FStar_Syntax_Syntax.Assumption :: uu____6725  in
              {
                FStar_Syntax_Syntax.sigel = uu____6713;
                FStar_Syntax_Syntax.sigrng =
                  (uu___1141_6712.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____6722;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___1141_6712.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___1141_6712.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____6731 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____6756 lbdef =
        match uu____6756 with
        | (uvs,t) ->
            let attrs =
              let uu____6767 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____6767
              then
<<<<<<< HEAD
                let uu____14831 =
                  let uu____14832 =
>>>>>>> snap
=======
                let uu____6772 =
                  let uu____6773 =
>>>>>>> snap
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
<<<<<<< HEAD
<<<<<<< HEAD
                  FStar_All.pipe_right uu____6697
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____6696 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___1150_6700 = s  in
            let uu____6701 =
              let uu____6704 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____6704  in
=======
                  FStar_All.pipe_right uu____14832
=======
                  FStar_All.pipe_right uu____6773
>>>>>>> snap
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____6772 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___1154_6776 = s  in
            let uu____6777 =
              let uu____6780 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
<<<<<<< HEAD
              FStar_Syntax_Syntax.Assumption :: uu____14839  in
>>>>>>> snap
=======
              FStar_Syntax_Syntax.Assumption :: uu____6780  in
>>>>>>> snap
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
<<<<<<< HEAD
                (uu___1150_6700.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____6701;
              FStar_Syntax_Syntax.sigmeta =
                (uu___1150_6700.FStar_Syntax_Syntax.sigmeta);
=======
                (uu___1989_14835.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____14836;
              FStar_Syntax_Syntax.sigmeta =
                (uu___1989_14835.FStar_Syntax_Syntax.sigmeta);
>>>>>>> snap
=======
                (uu___1154_6776.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____6777;
              FStar_Syntax_Syntax.sigmeta =
                (uu___1154_6776.FStar_Syntax_Syntax.sigmeta);
>>>>>>> snap
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
<<<<<<< HEAD
<<<<<<< HEAD
          | uu____6722 -> failwith "Impossible!"  in
        let c_opt =
          let uu____6729 = FStar_Syntax_Util.is_unit t  in
          if uu____6729
          then
            let uu____6736 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____6736
          else
            (let uu____6743 =
               let uu____6744 = FStar_Syntax_Subst.compress t  in
               uu____6744.FStar_Syntax_Syntax.n  in
             match uu____6743 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____6751,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____6775 -> FStar_Pervasives_Native.None)
=======
          | uu____14857 -> failwith "Impossible!"  in
=======
          | uu____6798 -> failwith "Impossible!"  in
>>>>>>> snap
        let c_opt =
          let uu____6805 = FStar_Syntax_Util.is_unit t  in
          if uu____6805
          then
            let uu____6812 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____6812
          else
            (let uu____6819 =
               let uu____6820 = FStar_Syntax_Subst.compress t  in
               uu____6820.FStar_Syntax_Syntax.n  in
             match uu____6819 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____6827,c) ->
                 FStar_Pervasives_Native.Some c
<<<<<<< HEAD
             | uu____14910 -> FStar_Pervasives_Native.None)
>>>>>>> snap
=======
             | uu____6851 -> FStar_Pervasives_Native.None)
>>>>>>> snap
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
<<<<<<< HEAD
<<<<<<< HEAD
            let uu____6787 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____6787
            then false
            else
              (let uu____6794 = FStar_Syntax_Util.is_pure_or_ghost_comp c  in
               if uu____6794
               then true
               else
                 (let uu____6801 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____6801))
         in
      let extract_sigelt s =
        (let uu____6813 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____6813
         then
           let uu____6816 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____6816
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____6823 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____6843 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____6862 ->
=======
            let uu____14922 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____14922
=======
            let uu____6863 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____6863
>>>>>>> snap
            then false
            else
              (let uu____6870 = FStar_Syntax_Util.is_pure_or_ghost_comp c  in
               if uu____6870
               then true
               else
                 (let uu____6877 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____6877))
         in
      let extract_sigelt s =
        (let uu____6889 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____6889
         then
           let uu____6892 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____6892
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____6899 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____6919 ->
             failwith "Impossible! extract_interface: bare data constructor"
<<<<<<< HEAD
         | FStar_Syntax_Syntax.Sig_splice uu____14997 ->
>>>>>>> snap
=======
         | FStar_Syntax_Syntax.Sig_splice uu____6938 ->
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
                             (lid,uu____6908,uu____6909,uu____6910,uu____6911,uu____6912)
                             ->
                             ((let uu____6922 =
                                 let uu____6925 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____6925  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____6922);
                              (let uu____6974 = vals_of_abstract_inductive s1
                                  in
                               FStar_List.append uu____6974 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____6978,uu____6979,uu____6980,uu____6981,uu____6982)
                             ->
                             ((let uu____6990 =
                                 let uu____6993 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____6993  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____6990);
                              sigelts1)
                         | uu____7042 ->
=======
                             (lid,uu____15043,uu____15044,uu____15045,uu____15046,uu____15047)
=======
                             (lid,uu____6984,uu____6985,uu____6986,uu____6987,uu____6988)
>>>>>>> snap
                             ->
                             ((let uu____6998 =
                                 let uu____7001 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____7001  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____6998);
                              (let uu____7050 = vals_of_abstract_inductive s1
                                  in
                               FStar_List.append uu____7050 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____7054,uu____7055,uu____7056,uu____7057,uu____7058)
                             ->
                             ((let uu____7066 =
                                 let uu____7069 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____7069  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____7066);
                              sigelts1)
<<<<<<< HEAD
                         | uu____15177 ->
>>>>>>> snap
=======
                         | uu____7118 ->
>>>>>>> snap
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
<<<<<<< HEAD
<<<<<<< HEAD
             let uu____7051 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____7051
=======
             let uu____15186 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15186
>>>>>>> snap
=======
             let uu____7127 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____7127
>>>>>>> snap
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
<<<<<<< HEAD
<<<<<<< HEAD
                 (let uu____7061 =
                    let uu___1214_7062 = s  in
                    let uu____7063 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1214_7062.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1214_7062.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____7063;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1214_7062.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1214_7062.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____7061])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____7074 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____7074
             then []
             else
               (let uu____7081 = lbs  in
                match uu____7081 with
=======
                 (let uu____15196 =
                    let uu___2053_15197 = s  in
                    let uu____15198 =
=======
                 (let uu____7137 =
                    let uu___1218_7138 = s  in
                    let uu____7139 =
>>>>>>> snap
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1218_7138.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1218_7138.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____7139;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1218_7138.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1218_7138.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____7137])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____7150 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____7150
             then []
             else
<<<<<<< HEAD
               (let uu____15216 = lbs  in
                match uu____15216 with
>>>>>>> snap
=======
               (let uu____7157 = lbs  in
                match uu____7157 with
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
                        (fun uu____7143  ->
                           match uu____7143 with
                           | (uu____7151,t,uu____7153) ->
=======
                        (fun uu____15278  ->
                           match uu____15278 with
                           | (uu____15286,t,uu____15288) ->
>>>>>>> snap
=======
                        (fun uu____7219  ->
                           match uu____7219 with
                           | (uu____7227,t,uu____7229) ->
>>>>>>> snap
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
<<<<<<< HEAD
<<<<<<< HEAD
                           fun uu____7170  ->
                             match uu____7170 with
=======
                           fun uu____15305  ->
                             match uu____15305 with
>>>>>>> snap
=======
                           fun uu____7246  ->
                             match uu____7246 with
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
                           (fun uu____7197  ->
                              match uu____7197 with
                              | (uu____7205,t,uu____7207) ->
=======
                           (fun uu____15332  ->
                              match uu____15332 with
                              | (uu____15340,t,uu____15342) ->
>>>>>>> snap
=======
                           (fun uu____7273  ->
                              match uu____7273 with
                              | (uu____7281,t,uu____7283) ->
>>>>>>> snap
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
<<<<<<< HEAD
<<<<<<< HEAD
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____7219,uu____7220) ->
=======
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____15354,uu____15355) ->
>>>>>>> snap
=======
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____7295,uu____7296) ->
>>>>>>> snap
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
<<<<<<< HEAD
<<<<<<< HEAD
                 let uu____7228 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____7257 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____7257) uu____7228
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____7261 =
                    let uu___1256_7262 = s  in
                    let uu____7263 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1256_7262.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1256_7262.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____7263;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1256_7262.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1256_7262.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____7261]
                else [])
             else
               (let uu____7270 =
                  let uu___1258_7271 = s  in
                  let uu____7272 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1258_7271.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1258_7271.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____7272;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1258_7271.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1258_7271.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____7270])
         | FStar_Syntax_Syntax.Sig_new_effect uu____7275 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7276 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____7277 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7278 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____7291 -> [s])
         in
      let uu___1270_7292 = m  in
      let uu____7293 =
        let uu____7294 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____7294 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___1270_7292.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____7293;
        FStar_Syntax_Syntax.exports =
          (uu___1270_7292.FStar_Syntax_Syntax.exports);
=======
                 let uu____15363 = FStar_ST.op_Bang abstract_inductive_tycons
=======
                 let uu____7304 = FStar_ST.op_Bang abstract_inductive_tycons
>>>>>>> snap
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____7333 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____7333) uu____7304
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____7337 =
                    let uu___1260_7338 = s  in
                    let uu____7339 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1260_7338.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1260_7338.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____7339;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1260_7338.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1260_7338.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____7337]
                else [])
             else
               (let uu____7346 =
                  let uu___1262_7347 = s  in
                  let uu____7348 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1262_7347.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1262_7347.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____7348;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1262_7347.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1262_7347.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____7346])
         | FStar_Syntax_Syntax.Sig_new_effect uu____7351 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7352 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____7353 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7354 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____7367 -> [s])
         in
      let uu___1274_7368 = m  in
      let uu____7369 =
        let uu____7370 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____7370 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___1274_7368.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____7369;
        FStar_Syntax_Syntax.exports =
<<<<<<< HEAD
          (uu___2109_15427.FStar_Syntax_Syntax.exports);
>>>>>>> snap
=======
          (uu___1274_7368.FStar_Syntax_Syntax.exports);
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
        (fun uu____7345  -> FStar_TypeChecker_Env.snapshot env msg)
=======
        (fun uu____15480  -> FStar_TypeChecker_Env.snapshot env msg)
>>>>>>> snap
=======
        (fun uu____7421  -> FStar_TypeChecker_Env.snapshot env msg)
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
          (fun uu____7392  ->
=======
          (fun uu____15527  ->
>>>>>>> snap
=======
          (fun uu____7468  ->
>>>>>>> snap
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____7407 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____7407
=======
      let uu____15542 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____15542
>>>>>>> snap
=======
      let uu____7483 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____7483
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
      (let uu____7496 = FStar_Options.debug_any ()  in
       if uu____7496
=======
      (let uu____15631 = FStar_Options.debug_any ()  in
       if uu____15631
>>>>>>> snap
=======
      (let uu____7572 = FStar_Options.debug_any ()  in
       if uu____7572
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
         let uu___1295_7512 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___1295_7512.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___1295_7512.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___1295_7512.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___1295_7512.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___1295_7512.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___1295_7512.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___1295_7512.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___1295_7512.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___1295_7512.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___1295_7512.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___1295_7512.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___1295_7512.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___1295_7512.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___1295_7512.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___1295_7512.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___1295_7512.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___1295_7512.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___1295_7512.FStar_TypeChecker_Env.use_eq);
=======
         let uu___2134_15647 = env  in
=======
         let uu___1299_7588 = env  in
>>>>>>> snap
         {
           FStar_TypeChecker_Env.solver =
             (uu___1299_7588.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___1299_7588.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___1299_7588.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___1299_7588.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___1299_7588.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___1299_7588.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___1299_7588.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___1299_7588.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___1299_7588.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___1299_7588.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___1299_7588.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___1299_7588.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___1299_7588.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___1299_7588.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___1299_7588.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___1299_7588.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___1299_7588.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
<<<<<<< HEAD
             (uu___2134_15647.FStar_TypeChecker_Env.use_eq);
>>>>>>> snap
=======
             (uu___1299_7588.FStar_TypeChecker_Env.use_eq);
>>>>>>> snap
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
<<<<<<< HEAD
<<<<<<< HEAD
             (uu___1295_7512.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___1295_7512.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___1295_7512.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___1295_7512.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___1295_7512.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___1295_7512.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___1295_7512.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___1295_7512.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___1295_7512.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___1295_7512.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___1295_7512.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___1295_7512.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___1295_7512.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___1295_7512.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___1295_7512.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
             (uu___2332_16587.FStar_TypeChecker_Env.synth_hook);
=======
             (uu___2330_16669.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___2330_16669.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
             (uu___2306_16500.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___2306_16500.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
             (uu___1295_7512.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___1295_7512.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
           FStar_TypeChecker_Env.splice =
             (uu___1295_7512.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___1295_7512.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___1295_7512.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___1295_7512.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___1295_7512.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___1295_7512.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___1295_7512.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___1295_7512.FStar_TypeChecker_Env.strict_args_tab)
=======
             (uu___2134_15647.FStar_TypeChecker_Env.lax);
=======
             (uu___1299_7588.FStar_TypeChecker_Env.lax);
>>>>>>> snap
           FStar_TypeChecker_Env.lax_universes =
             (uu___1299_7588.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___1299_7588.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___1299_7588.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___1299_7588.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___1299_7588.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___1299_7588.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___1299_7588.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___1299_7588.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___1299_7588.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___1299_7588.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___1299_7588.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___1299_7588.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___1299_7588.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___1299_7588.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___1299_7588.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___1299_7588.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___1299_7588.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___1299_7588.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___1299_7588.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___1299_7588.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___1299_7588.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___1299_7588.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___1299_7588.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
<<<<<<< HEAD
             (uu___2134_15647.FStar_TypeChecker_Env.strict_args_tab)
>>>>>>> snap
=======
             (uu___1299_7588.FStar_TypeChecker_Env.strict_args_tab)
>>>>>>> snap
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
<<<<<<< HEAD
<<<<<<< HEAD
       let uu____7514 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____7514 with
       | (ses,exports,env3) ->
           ((let uu___1303_7547 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___1303_7547.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___1303_7547.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___1303_7547.FStar_Syntax_Syntax.is_interface)
=======
       let uu____15649 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
=======
       let uu____7590 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
>>>>>>> snap
          in
       match uu____7590 with
       | (ses,exports,env3) ->
           ((let uu___1307_7623 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___1307_7623.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___1307_7623.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
<<<<<<< HEAD
                 (uu___2142_15682.FStar_Syntax_Syntax.is_interface)
>>>>>>> snap
=======
                 (uu___1307_7623.FStar_Syntax_Syntax.is_interface)
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____7576 = tc_decls env decls  in
        match uu____7576 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___1312_7607 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___1312_7607.FStar_Syntax_Syntax.name);
=======
        let uu____15711 = tc_decls env decls  in
        match uu____15711 with
=======
        let uu____7652 = tc_decls env decls  in
        match uu____7652 with
>>>>>>> snap
        | (ses,exports,env1) ->
            let modul1 =
              let uu___1316_7683 = modul  in
              {
                FStar_Syntax_Syntax.name =
<<<<<<< HEAD
                  (uu___2151_15742.FStar_Syntax_Syntax.name);
>>>>>>> snap
=======
                  (uu___1316_7683.FStar_Syntax_Syntax.name);
>>>>>>> snap
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
<<<<<<< HEAD
<<<<<<< HEAD
                  (uu___1312_7607.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___1312_7607.FStar_Syntax_Syntax.is_interface)
=======
                  (uu___2151_15742.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___2151_15742.FStar_Syntax_Syntax.is_interface)
>>>>>>> snap
=======
                  (uu___1316_7683.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___1316_7683.FStar_Syntax_Syntax.is_interface)
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____7668 = tc_partial_modul env01 m  in
        match uu____7668 with
=======
        let uu____15803 = tc_partial_modul env01 m  in
        match uu____15803 with
>>>>>>> snap
=======
        let uu____7744 = tc_partial_modul env01 m  in
        match uu____7744 with
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
                (let uu____7705 = FStar_Errors.get_err_count ()  in
                 uu____7705 = Prims.int_zero)
=======
                (let uu____15840 = FStar_Errors.get_err_count ()  in
                 uu____15840 = Prims.int_zero)
>>>>>>> snap
=======
                (let uu____7781 = FStar_Errors.get_err_count ()  in
                 uu____7781 = Prims.int_zero)
>>>>>>> snap
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
<<<<<<< HEAD
<<<<<<< HEAD
              ((let uu____7716 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____7716
                then
                  let uu____7720 =
                    let uu____7722 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____7722 then "" else " (in lax mode) "  in
                  let uu____7730 =
                    let uu____7732 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____7732
                    then
                      let uu____7736 =
                        let uu____7738 = FStar_Syntax_Print.modul_to_string m
                           in
                        Prims.op_Hat uu____7738 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____7736
                    else ""  in
                  let uu____7745 =
                    let uu____7747 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____7747
                    then
                      let uu____7751 =
                        let uu____7753 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____7753 "\n"  in
                      Prims.op_Hat "\nto: " uu____7751
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____7720
                    uu____7730 uu____7745
=======
              ((let uu____15851 =
=======
              ((let uu____7792 =
>>>>>>> snap
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____7792
                then
                  let uu____7796 =
                    let uu____7798 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____7798 then "" else " (in lax mode) "  in
                  let uu____7806 =
                    let uu____7808 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____7808
                    then
                      let uu____7812 =
                        let uu____7814 = FStar_Syntax_Print.modul_to_string m
                           in
                        Prims.op_Hat uu____7814 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____7812
                    else ""  in
                  let uu____7821 =
                    let uu____7823 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____7823
                    then
                      let uu____7827 =
                        let uu____7829 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____7829 "\n"  in
                      Prims.op_Hat "\nto: " uu____7827
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
<<<<<<< HEAD
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____15855
                    uu____15865 uu____15880
>>>>>>> snap
=======
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____7796
                    uu____7806 uu____7821
>>>>>>> snap
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
<<<<<<< HEAD
<<<<<<< HEAD
                    let uu___1338_7767 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1338_7767.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1338_7767.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1338_7767.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1338_7767.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1338_7767.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1338_7767.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1338_7767.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1338_7767.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1338_7767.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1338_7767.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1338_7767.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1338_7767.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1338_7767.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1338_7767.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1338_7767.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1338_7767.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1338_7767.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1338_7767.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1338_7767.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1338_7767.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1338_7767.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1338_7767.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1338_7767.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1338_7767.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1338_7767.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1338_7767.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1338_7767.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1338_7767.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1338_7767.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1338_7767.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1338_7767.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1338_7767.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1338_7767.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1338_7767.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1338_7767.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                        (uu___2375_16842.FStar_TypeChecker_Env.synth_hook);
=======
                        (uu___2373_16924.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___2373_16924.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                        (uu___2349_16755.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___2349_16755.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                        (uu___1338_7767.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1338_7767.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
                      FStar_TypeChecker_Env.splice =
                        (uu___1338_7767.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1338_7767.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1338_7767.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1338_7767.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1338_7767.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1338_7767.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1338_7767.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let en02 =
                    let uu___1341_7769 = en01  in
                    let uu____7770 =
                      let uu____7785 =
=======
                    let uu___2177_15902 = en0  in
=======
                    let uu___1342_7843 = en0  in
>>>>>>> snap
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1342_7843.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1342_7843.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1342_7843.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1342_7843.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1342_7843.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1342_7843.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1342_7843.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1342_7843.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1342_7843.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1342_7843.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1342_7843.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1342_7843.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1342_7843.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1342_7843.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1342_7843.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1342_7843.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1342_7843.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1342_7843.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1342_7843.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1342_7843.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1342_7843.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1342_7843.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1342_7843.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1342_7843.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1342_7843.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1342_7843.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1342_7843.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1342_7843.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1342_7843.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1342_7843.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1342_7843.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1342_7843.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1342_7843.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1342_7843.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1342_7843.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1342_7843.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1342_7843.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1342_7843.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1342_7843.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1342_7843.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1342_7843.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1342_7843.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1342_7843.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1342_7843.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let en02 =
<<<<<<< HEAD
                    let uu___2180_15904 = en01  in
                    let uu____15905 =
                      let uu____15920 =
>>>>>>> snap
=======
                    let uu___1345_7845 = en01  in
                    let uu____7846 =
                      let uu____7861 =
>>>>>>> snap
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
<<<<<<< HEAD
<<<<<<< HEAD
                      (uu____7785, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1341_7769.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1341_7769.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1341_7769.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1341_7769.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1341_7769.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1341_7769.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1341_7769.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1341_7769.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1341_7769.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1341_7769.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1341_7769.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1341_7769.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1341_7769.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1341_7769.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1341_7769.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1341_7769.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1341_7769.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1341_7769.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1341_7769.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1341_7769.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1341_7769.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1341_7769.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1341_7769.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1341_7769.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1341_7769.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1341_7769.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1341_7769.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1341_7769.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1341_7769.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1341_7769.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1341_7769.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____7770;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1341_7769.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1341_7769.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1341_7769.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                        (uu___2378_16844.FStar_TypeChecker_Env.synth_hook);
=======
                        (uu___2376_16926.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___2376_16926.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                        (uu___2352_16757.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___2352_16757.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                        (uu___1341_7769.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1341_7769.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
                      FStar_TypeChecker_Env.splice =
                        (uu___1341_7769.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1341_7769.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1341_7769.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1341_7769.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1341_7769.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1341_7769.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1341_7769.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1341_7769.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let uu____7831 =
                    let uu____7833 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____7833  in
                  if uu____7831
                  then
                    ((let uu____7837 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____7837 (fun a2  -> ()));
                     en02)
                  else en02  in
                let uu____7841 = tc_modul en0 modul_iface true  in
                match uu____7841 with
                | (modul_iface1,env) ->
                    ((let uu___1350_7854 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___1350_7854.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___1350_7854.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___1350_7854.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___1352_7858 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___1352_7858.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___1352_7858.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___1352_7858.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____7861 =
=======
                      (uu____15920, FStar_Pervasives_Native.None)  in
=======
                      (uu____7861, FStar_Pervasives_Native.None)  in
>>>>>>> snap
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1345_7845.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1345_7845.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1345_7845.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1345_7845.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1345_7845.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1345_7845.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1345_7845.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1345_7845.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1345_7845.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1345_7845.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1345_7845.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1345_7845.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1345_7845.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1345_7845.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1345_7845.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1345_7845.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1345_7845.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1345_7845.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1345_7845.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1345_7845.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1345_7845.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1345_7845.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1345_7845.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1345_7845.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1345_7845.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1345_7845.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1345_7845.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1345_7845.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1345_7845.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1345_7845.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1345_7845.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____7846;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1345_7845.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1345_7845.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1345_7845.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1345_7845.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1345_7845.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1345_7845.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1345_7845.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1345_7845.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1345_7845.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1345_7845.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1345_7845.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1345_7845.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1345_7845.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let uu____7907 =
                    let uu____7909 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____7909  in
                  if uu____7907
                  then
                    ((let uu____7913 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____7913 (fun a2  -> ()));
                     en02)
                  else en02  in
                let uu____7917 = tc_modul en0 modul_iface true  in
                match uu____7917 with
                | (modul_iface1,env) ->
                    ((let uu___1354_7930 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___1354_7930.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___1354_7930.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___1354_7930.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___1356_7934 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___1356_7934.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___1356_7934.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___1356_7934.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
<<<<<<< HEAD
               (let uu____15996 =
>>>>>>> snap
=======
               (let uu____7937 =
>>>>>>> snap
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
<<<<<<< HEAD
<<<<<<< HEAD
                FStar_All.pipe_right uu____7861 FStar_Util.smap_clear);
               (let uu____7897 =
                  ((let uu____7901 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____7901) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____7904 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____7904)
                   in
                if uu____7897 then check_exports env modul exports else ());
               (let uu____7910 =
=======
                FStar_All.pipe_right uu____15996 FStar_Util.smap_clear);
               (let uu____16032 =
                  ((let uu____16036 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____16036) &&
=======
                FStar_All.pipe_right uu____7937 FStar_Util.smap_clear);
               (let uu____7973 =
                  ((let uu____7977 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____7977) &&
>>>>>>> snap
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____7980 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____7980)
                   in
<<<<<<< HEAD
                if uu____16032 then check_exports env modul exports else ());
               (let uu____16045 =
>>>>>>> snap
=======
                if uu____7973 then check_exports env modul exports else ());
               (let uu____7986 =
>>>>>>> snap
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
<<<<<<< HEAD
<<<<<<< HEAD
                FStar_All.pipe_right uu____7910 (fun a3  -> ()));
=======
                FStar_All.pipe_right uu____16045 (fun a4  -> ()));
>>>>>>> snap
=======
                FStar_All.pipe_right uu____7986 (fun a3  -> ()));
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____7925 =
          let uu____7927 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____7927  in
        push_context env uu____7925  in
=======
        let uu____16060 =
          let uu____16062 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____16062  in
        push_context env uu____16060  in
>>>>>>> snap
=======
        let uu____8001 =
          let uu____8003 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____8003  in
        push_context env uu____8001  in
>>>>>>> snap
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = add_sigelt_to_env env2 se true  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
<<<<<<< HEAD
<<<<<<< HEAD
                       let uu____7948 =
=======
                       let uu____16084 =
>>>>>>> snap
=======
                       let uu____8025 =
>>>>>>> snap
                         FStar_TypeChecker_Env.lookup_sigelt env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____7951 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____7951 with | (uu____7958,env3) -> env3
=======
      let uu____16087 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____16087 with | (uu____16094,env3) -> env3
>>>>>>> snap
=======
      let uu____8028 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____8028 with | (uu____8035,env3) -> env3
>>>>>>> snap
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
<<<<<<< HEAD
<<<<<<< HEAD
        (let uu____7983 = FStar_Options.debug_any ()  in
         if uu____7983
         then
           let uu____7986 =
=======
        (let uu____16119 = FStar_Options.debug_any ()  in
         if uu____16119
         then
           let uu____16122 =
>>>>>>> snap
=======
        (let uu____8060 = FStar_Options.debug_any ()  in
         if uu____8060
         then
           let uu____8063 =
>>>>>>> snap
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
<<<<<<< HEAD
<<<<<<< HEAD
              else "module") uu____7986
         else ());
        (let uu____7998 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____7998
         then
           let uu____8001 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____8001
         else ());
        (let env1 =
           let uu___1382_8007 = env  in
           let uu____8008 =
             let uu____8010 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____8010  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___1382_8007.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___1382_8007.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___1382_8007.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___1382_8007.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___1382_8007.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___1382_8007.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___1382_8007.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___1382_8007.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___1382_8007.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___1382_8007.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___1382_8007.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___1382_8007.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___1382_8007.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___1382_8007.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___1382_8007.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___1382_8007.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___1382_8007.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___1382_8007.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___1382_8007.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___1382_8007.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____8008;
             FStar_TypeChecker_Env.lax_universes =
               (uu___1382_8007.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___1382_8007.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___1382_8007.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___1382_8007.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___1382_8007.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___1382_8007.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___1382_8007.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___1382_8007.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___1382_8007.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___1382_8007.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___1382_8007.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___1382_8007.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___1382_8007.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___1382_8007.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
               (uu___2419_17082.FStar_TypeChecker_Env.synth_hook);
=======
               (uu___2417_17164.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___2417_17164.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
               (uu___2393_16995.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___2393_16995.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
               (uu___1382_8007.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___1382_8007.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
             FStar_TypeChecker_Env.splice =
               (uu___1382_8007.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___1382_8007.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___1382_8007.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___1382_8007.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___1382_8007.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___1382_8007.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___1382_8007.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___1382_8007.FStar_TypeChecker_Env.strict_args_tab)
           }  in
         let uu____8012 = tc_modul env1 m b  in
         match uu____8012 with
         | (m1,env2) ->
             ((let uu____8024 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____8024
               then
                 let uu____8027 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____8027
               else ());
              (let uu____8033 =
=======
              else "module") uu____16122
=======
              else "module") uu____8063
>>>>>>> snap
         else ());
        (let uu____8075 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____8075
         then
           let uu____8078 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____8078
         else ());
        (let env1 =
           let uu___1386_8084 = env  in
           let uu____8085 =
             let uu____8087 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____8087  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___1386_8084.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___1386_8084.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___1386_8084.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___1386_8084.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___1386_8084.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___1386_8084.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___1386_8084.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___1386_8084.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___1386_8084.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___1386_8084.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___1386_8084.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___1386_8084.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___1386_8084.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___1386_8084.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___1386_8084.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___1386_8084.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___1386_8084.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___1386_8084.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___1386_8084.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___1386_8084.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____8085;
             FStar_TypeChecker_Env.lax_universes =
               (uu___1386_8084.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___1386_8084.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___1386_8084.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___1386_8084.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___1386_8084.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___1386_8084.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___1386_8084.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___1386_8084.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___1386_8084.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___1386_8084.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___1386_8084.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___1386_8084.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___1386_8084.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___1386_8084.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___1386_8084.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___1386_8084.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___1386_8084.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___1386_8084.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___1386_8084.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___1386_8084.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___1386_8084.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___1386_8084.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___1386_8084.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___1386_8084.FStar_TypeChecker_Env.strict_args_tab)
           }  in
         let uu____8089 = tc_modul env1 m b  in
         match uu____8089 with
         | (m1,env2) ->
             ((let uu____8101 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____8101
               then
                 let uu____8104 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____8104
               else ());
<<<<<<< HEAD
              (let uu____16169 =
>>>>>>> snap
=======
              (let uu____8110 =
>>>>>>> snap
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
<<<<<<< HEAD
<<<<<<< HEAD
               if uu____8033
=======
               if uu____16169
>>>>>>> snap
=======
               if uu____8110
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
                         let uu____8071 =
=======
                         let uu____16207 =
>>>>>>> snap
=======
                         let uu____8148 =
>>>>>>> snap
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
<<<<<<< HEAD
<<<<<<< HEAD
                         match uu____8071 with
                         | (univnames1,e) ->
                             let uu___1404_8078 = lb  in
                             let uu____8079 =
                               let uu____8082 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____8082 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1404_8078.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1404_8078.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1404_8078.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1404_8078.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____8079;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1404_8078.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1404_8078.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___1406_8083 = se  in
                       let uu____8084 =
                         let uu____8085 =
                           let uu____8092 =
                             let uu____8093 = FStar_List.map update lbs  in
                             (b1, uu____8093)  in
                           (uu____8092, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____8085  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____8084;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1406_8083.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1406_8083.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1406_8083.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___1406_8083.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____8101 -> se  in
                 let normalized_module =
                   let uu___1410_8103 = m1  in
                   let uu____8104 =
=======
                         match uu____16207 with
=======
                         match uu____8148 with
>>>>>>> snap
                         | (univnames1,e) ->
                             let uu___1408_8155 = lb  in
                             let uu____8156 =
                               let uu____8159 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____8159 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1408_8155.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1408_8155.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1408_8155.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1408_8155.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____8156;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1408_8155.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1408_8155.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___1410_8160 = se  in
                       let uu____8161 =
                         let uu____8162 =
                           let uu____8169 =
                             let uu____8170 = FStar_List.map update lbs  in
                             (b1, uu____8170)  in
                           (uu____8169, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____8162  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____8161;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1410_8160.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1410_8160.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1410_8160.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___1410_8160.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____8178 -> se  in
                 let normalized_module =
<<<<<<< HEAD
                   let uu___2249_16239 = m1  in
                   let uu____16240 =
>>>>>>> snap
=======
                   let uu___1414_8180 = m1  in
                   let uu____8181 =
>>>>>>> snap
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
<<<<<<< HEAD
<<<<<<< HEAD
                       (uu___1410_8103.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____8104;
                     FStar_Syntax_Syntax.exports =
                       (uu___1410_8103.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___1410_8103.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____8105 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____8105
=======
                       (uu___2249_16239.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____16240;
=======
                       (uu___1414_8180.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____8181;
>>>>>>> snap
                     FStar_Syntax_Syntax.exports =
                       (uu___1414_8180.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___1414_8180.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____8182 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
<<<<<<< HEAD
                 FStar_Util.print1 "%s\n" uu____16241
>>>>>>> snap
=======
                 FStar_Util.print1 "%s\n" uu____8182
>>>>>>> snap
               else ());
              (m1, env2)))
  