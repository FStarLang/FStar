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
                         let x_a = fresh_x_a "x" a  in
                         let rest_bs =
                           let uu____1257 =
                             let uu____1258 = FStar_Syntax_Subst.compress ty
                                in
                             uu____1258.FStar_Syntax_Syntax.n  in
                           match uu____1257 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1270)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____1298 =
                                 FStar_Syntax_Subst.open_binders bs  in
                               (match uu____1298 with
                                | (a',uu____1308)::(x_a',uu____1310)::bs1 ->
                                    let substs =
                                      let uu____1343 =
                                        let uu____1344 =
                                          let uu____1351 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              (FStar_Pervasives_Native.fst a)
                                             in
                                          (a', uu____1351)  in
                                        FStar_Syntax_Syntax.NT uu____1344  in
                                      let uu____1358 =
                                        let uu____1361 =
                                          let uu____1362 =
                                            let uu____1369 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   x_a)
                                               in
                                            (x_a', uu____1369)  in
                                          FStar_Syntax_Syntax.NT uu____1362
                                           in
                                        [uu____1361]  in
                                      uu____1343 :: uu____1358  in
                                    FStar_Syntax_Subst.subst_binders substs
                                      bs1
                                | uu____1376 -> failwith "Impossible!")
                           | uu____1386 ->
                               FStar_Errors.raise_error
                                 (FStar_Errors.Fatal_UnexpectedEffect, "") r
                            in
                         let bs = a :: x_a :: rest_bs  in
                         let uu____1418 =
                           let uu____1423 =
                             FStar_TypeChecker_Env.push_binders env bs  in
                           let uu____1424 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.fst a)
                               FStar_Syntax_Syntax.bv_to_name
                              in
                           fresh_repr r uu____1423 u_a uu____1424  in
                         (match uu____1418 with
                          | (repr1,g) ->
                              let k =
                                let uu____1444 =
                                  FStar_Syntax_Syntax.mk_Total' repr1
                                    (FStar_Pervasives_Native.Some u_a)
                                   in
                                FStar_Syntax_Util.arrow bs uu____1444  in
                              let g_eq = FStar_TypeChecker_Rel.teq env ty k
                                 in
                              ((let uu____1449 =
                                  FStar_TypeChecker_Env.conj_guard g g_eq  in
                                FStar_TypeChecker_Rel.force_trivial_guard env
                                  uu____1449);
                               (let uu____1450 =
                                  let uu____1453 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env k
                                     in
                                  FStar_Syntax_Subst.close_univ_vars us
                                    uu____1453
                                   in
                                (ret_us, ret_t, uu____1450))))))
            in
         log_combinator "return_repr" return_repr;
         (let bind_repr =
            let r =
              (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
               in
            let uu____1480 =
              check_and_gen' "bind_repr" (Prims.of_int (2))
                FStar_Pervasives_Native.None ed.FStar_Syntax_Syntax.bind_repr
               in
            match uu____1480 with
            | (bind_us,bind_t,bind_ty) ->
                let uu____1504 =
                  FStar_Syntax_Subst.open_univ_vars bind_us bind_ty  in
                (match uu____1504 with
                 | (us,ty) ->
                     let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                        in
                     let uu____1524 = fresh_a_and_u_a "a"  in
                     (match uu____1524 with
                      | (a,u_a) ->
                          let uu____1544 = fresh_a_and_u_a "b"  in
                          (match uu____1544 with
                           | (b,u_b) ->
                               let rest_bs =
                                 let uu____1573 =
                                   let uu____1574 =
                                     FStar_Syntax_Subst.compress ty  in
                                   uu____1574.FStar_Syntax_Syntax.n  in
                                 match uu____1573 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____1586) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (4))
                                     ->
                                     let uu____1614 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____1614 with
                                      | (a',uu____1624)::(b',uu____1626)::bs1
                                          ->
                                          let uu____1656 =
                                            FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 (Prims.of_int (2))) bs1
                                             in
                                          (match uu____1656 with
                                           | (bs2,uu____1699) ->
                                               let substs =
                                                 let uu____1735 =
                                                   let uu____1736 =
                                                     let uu____1743 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a)
                                                        in
                                                     (a', uu____1743)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____1736
                                                    in
                                                 let uu____1750 =
                                                   let uu____1753 =
                                                     let uu____1754 =
                                                       let uu____1761 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              b)
                                                          in
                                                       (b', uu____1761)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____1754
                                                      in
                                                   [uu____1753]  in
                                                 uu____1735 :: uu____1750  in
                                               FStar_Syntax_Subst.subst_binders
                                                 substs bs2)
                                      | uu____1768 -> failwith "Impossible!")
                                 | uu____1778 ->
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_UnexpectedEffect,
                                         "") r
                                  in
                               let bs = a :: b :: rest_bs  in
                               let uu____1810 =
                                 let uu____1821 =
                                   let uu____1826 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____1827 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____1826 u_a uu____1827  in
                                 match uu____1821 with
                                 | (repr1,g) ->
                                     let uu____1842 =
                                       let uu____1849 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None repr1
                                          in
                                       FStar_All.pipe_right uu____1849
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____1842, g)
                                  in
                               (match uu____1810 with
                                | (f,g_f) ->
                                    let uu____1889 =
                                      let x_a = fresh_x_a "x" a  in
                                      let uu____1902 =
                                        let uu____1907 =
                                          FStar_TypeChecker_Env.push_binders
                                            env (FStar_List.append bs [x_a])
                                           in
                                        let uu____1926 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst b)
                                            FStar_Syntax_Syntax.bv_to_name
                                           in
                                        fresh_repr r uu____1907 u_b
                                          uu____1926
                                         in
                                      match uu____1902 with
                                      | (repr1,g) ->
                                          let uu____1941 =
                                            let uu____1948 =
                                              let uu____1949 =
                                                let uu____1950 =
                                                  FStar_Syntax_Syntax.mk_Total'
                                                    repr1
                                                    (FStar_Pervasives_Native.Some
                                                       u_b)
                                                   in
                                                FStar_Syntax_Util.arrow 
                                                  [x_a] uu____1950
                                                 in
                                              FStar_Syntax_Syntax.gen_bv "g"
                                                FStar_Pervasives_Native.None
                                                uu____1949
                                               in
                                            FStar_All.pipe_right uu____1948
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          (uu____1941, g)
                                       in
                                    (match uu____1889 with
                                     | (g,g_g) ->
                                         let uu____2004 =
                                           let uu____2009 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____2010 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst b)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____2009 u_b
                                             uu____2010
                                            in
                                         (match uu____2004 with
                                          | (repr1,g_repr) ->
                                              let k =
                                                let uu____2030 =
                                                  FStar_Syntax_Syntax.mk_Total'
                                                    repr1
                                                    (FStar_Pervasives_Native.Some
                                                       u_b)
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  (FStar_List.append bs
                                                     [f; g]) uu____2030
                                                 in
                                              let g_eq =
                                                FStar_TypeChecker_Rel.teq env
                                                  ty k
                                                 in
                                              (FStar_List.iter
                                                 (FStar_TypeChecker_Rel.force_trivial_guard
                                                    env)
                                                 [g_f; g_g; g_repr; g_eq];
                                               (let uu____2059 =
                                                  let uu____2062 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Beta]
                                                      env k
                                                     in
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    bind_us uu____2062
                                                   in
                                                (bind_us, bind_t, uu____2059)))))))))
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
             let uu____2104 =
               check_and_gen' "stronger_repr" Prims.int_one
                 FStar_Pervasives_Native.None stronger_repr
                in
             match uu____2104 with
             | (stronger_us,stronger_t,stronger_ty) ->
                 ((let uu____2129 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                       (FStar_Options.Other "LayeredEffects")
                      in
                   if uu____2129
                   then
                     let uu____2134 =
                       FStar_Syntax_Print.tscheme_to_string
                         (stronger_us, stronger_t)
                        in
                     let uu____2140 =
                       FStar_Syntax_Print.tscheme_to_string
                         (stronger_us, stronger_ty)
                        in
                     FStar_Util.print2
                       "stronger combinator typechecked with term: %s and type: %s\n"
                       uu____2134 uu____2140
                   else ());
                  (let uu____2149 =
                     FStar_Syntax_Subst.open_univ_vars stronger_us
                       stronger_ty
                      in
                   match uu____2149 with
                   | (us,ty) ->
                       let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                          in
                       let uu____2169 = fresh_a_and_u_a "a"  in
                       (match uu____2169 with
                        | (a,u) ->
                            let f_is_bs =
                              let signature_ts =
                                let uu____2191 = signature  in
                                match uu____2191 with
                                | (us1,t,uu____2206) -> (us1, t)  in
                              let uu____2223 =
                                let uu____2224 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____2224
                                  FStar_Syntax_Syntax.bv_to_name
                                 in
                              FStar_TypeChecker_Util.layered_effect_indices_as_binders
                                signature_ts u uu____2223
                               in
                            let g_is_bs =
                              let signature_ts =
                                let uu____2235 = signature  in
                                match uu____2235 with
                                | (us1,t,uu____2250) -> (us1, t)  in
                              let uu____2267 =
                                let uu____2268 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____2268
                                  FStar_Syntax_Syntax.bv_to_name
                                 in
                              FStar_TypeChecker_Util.layered_effect_indices_as_binders
                                signature_ts u uu____2267
                               in
                            let f_b =
                              let repr_ts =
                                let uu____2285 = repr  in
                                match uu____2285 with
                                | (us1,t,uu____2300) -> (us1, t)  in
                              let uu____2317 =
                                FStar_TypeChecker_Env.inst_tscheme_with
                                  repr_ts [u]
                                 in
                              match uu____2317 with
                              | (uu____2328,repr1) ->
                                  let repr2 =
                                    let uu____2333 =
                                      let uu____2338 =
                                        let uu____2339 =
                                          let uu____2342 =
                                            FStar_All.pipe_right (a ::
                                              f_is_bs)
                                              (FStar_List.map
                                                 FStar_Pervasives_Native.fst)
                                             in
                                          FStar_All.pipe_right uu____2342
                                            (FStar_List.map
                                               FStar_Syntax_Syntax.bv_to_name)
                                           in
                                        FStar_All.pipe_right uu____2339
                                          (FStar_List.map
                                             FStar_Syntax_Syntax.as_arg)
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app repr1
                                        uu____2338
                                       in
                                    uu____2333 FStar_Pervasives_Native.None r
                                     in
                                  let uu____2375 =
                                    FStar_Syntax_Syntax.gen_bv "f"
                                      FStar_Pervasives_Native.None repr2
                                     in
                                  FStar_All.pipe_right uu____2375
                                    FStar_Syntax_Syntax.mk_binder
                               in
                            let ret_t =
                              let repr_ts =
                                let uu____2387 = repr  in
                                match uu____2387 with
                                | (us1,t,uu____2402) -> (us1, t)  in
                              let uu____2419 =
                                FStar_TypeChecker_Env.inst_tscheme_with
                                  repr_ts [u]
                                 in
                              match uu____2419 with
                              | (uu____2426,repr1) ->
                                  let uu____2428 =
                                    let uu____2433 =
                                      let uu____2434 =
                                        let uu____2437 =
                                          FStar_All.pipe_right (a :: g_is_bs)
                                            (FStar_List.map
                                               FStar_Pervasives_Native.fst)
                                           in
                                        FStar_All.pipe_right uu____2437
                                          (FStar_List.map
                                             FStar_Syntax_Syntax.bv_to_name)
                                         in
                                      FStar_All.pipe_right uu____2434
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.as_arg)
                                       in
                                    FStar_Syntax_Syntax.mk_Tm_app repr1
                                      uu____2433
                                     in
                                  uu____2428 FStar_Pervasives_Native.None r
                               in
                            let pure_wp_t =
                              let pure_wp_ts =
                                let uu____2472 =
                                  FStar_TypeChecker_Env.lookup_definition
                                    [FStar_TypeChecker_Env.NoDelta] env
                                    FStar_Parser_Const.pure_wp_lid
                                   in
                                FStar_All.pipe_right uu____2472
                                  FStar_Util.must
                                 in
                              let uu____2489 =
                                FStar_TypeChecker_Env.inst_tscheme pure_wp_ts
                                 in
                              match uu____2489 with
                              | (uu____2494,pure_wp_t) ->
                                  let uu____2496 =
                                    let uu____2501 =
                                      let uu____2502 =
                                        FStar_All.pipe_right ret_t
                                          FStar_Syntax_Syntax.as_arg
                                         in
                                      [uu____2502]  in
                                    FStar_Syntax_Syntax.mk_Tm_app pure_wp_t
                                      uu____2501
                                     in
                                  uu____2496 FStar_Pervasives_Native.None r
                               in
                            let uu____2535 =
                              let uu____2548 =
                                FStar_TypeChecker_Env.push_binders env (a ::
                                  (FStar_List.append f_is_bs g_is_bs))
                                 in
                              FStar_TypeChecker_Util.new_implicit_var "" r
                                uu____2548 pure_wp_t
                               in
                            (match uu____2535 with
                             | (pure_wp_uvar,uu____2575,g_pure_wp_uvar) ->
                                 let c =
                                   let uu____2590 =
                                     let uu____2591 =
                                       let uu____2592 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       [uu____2592]  in
                                     let uu____2593 =
                                       let uu____2604 =
                                         FStar_All.pipe_right pure_wp_uvar
                                           FStar_Syntax_Syntax.as_arg
                                          in
                                       [uu____2604]  in
                                     {
                                       FStar_Syntax_Syntax.comp_univs =
                                         uu____2591;
                                       FStar_Syntax_Syntax.effect_name =
                                         FStar_Parser_Const.effect_PURE_lid;
                                       FStar_Syntax_Syntax.result_typ = ret_t;
                                       FStar_Syntax_Syntax.effect_args =
                                         uu____2593;
                                       FStar_Syntax_Syntax.flags = []
                                     }  in
                                   FStar_Syntax_Syntax.mk_Comp uu____2590  in
                                 let k =
                                   FStar_Syntax_Util.arrow (a ::
                                     (FStar_List.append f_is_bs
                                        (FStar_List.append g_is_bs [f_b]))) c
                                    in
                                 ((let uu____2671 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "LayeredEffects")
                                      in
                                   if uu____2671
                                   then
                                     let uu____2676 =
                                       FStar_Syntax_Print.term_to_string k
                                        in
                                     FStar_Util.print1
                                       "Expected type before unification: %s\n"
                                       uu____2676
                                   else ());
                                  (let g = FStar_TypeChecker_Rel.teq env ty k
                                      in
                                   (let uu____2683 =
                                      FStar_TypeChecker_Env.conj_guard
                                        g_pure_wp_uvar g
                                       in
                                    FStar_TypeChecker_Rel.force_trivial_guard
                                      env uu____2683);
                                   (let k1 =
                                      let k1 =
                                        FStar_TypeChecker_Normalize.remove_uvar_solutions
                                          env k
                                         in
                                      let uu____2686 =
                                        let uu____2687 =
                                          FStar_Syntax_Subst.compress k1  in
                                        uu____2687.FStar_Syntax_Syntax.n  in
                                      match uu____2686 with
                                      | FStar_Syntax_Syntax.Tm_arrow 
                                          (bs,c1) ->
                                          let uu____2712 =
                                            FStar_Syntax_Subst.open_comp bs
                                              c1
                                             in
                                          (match uu____2712 with
                                           | (bs1,c2) ->
                                               let uu____2719 =
                                                 let uu____2726 =
                                                   FStar_All.pipe_right c2
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2726
                                                   FStar_Syntax_Util.destruct_comp
                                                  in
                                               (match uu____2719 with
                                                | (u1,uu____2734,wp) ->
                                                    let trivial_post =
                                                      let ts =
                                                        let uu____2738 =
                                                          FStar_TypeChecker_Env.lookup_definition
                                                            [FStar_TypeChecker_Env.NoDelta]
                                                            env
                                                            FStar_Parser_Const.trivial_pure_post_lid
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____2738
                                                          FStar_Util.must
                                                         in
                                                      let uu____2755 =
                                                        FStar_TypeChecker_Env.inst_tscheme_with
                                                          ts [u1]
                                                         in
                                                      match uu____2755 with
                                                      | (uu____2760,t) ->
                                                          let uu____2762 =
                                                            let uu____2767 =
                                                              let uu____2768
                                                                =
                                                                FStar_All.pipe_right
                                                                  ret_t
                                                                  FStar_Syntax_Syntax.as_arg
                                                                 in
                                                              [uu____2768]
                                                               in
                                                            FStar_Syntax_Syntax.mk_Tm_app
                                                              t uu____2767
                                                             in
                                                          uu____2762
                                                            FStar_Pervasives_Native.None
                                                            r
                                                       in
                                                    let fml =
                                                      let uu____2804 =
                                                        let uu____2809 =
                                                          let uu____2810 =
                                                            FStar_All.pipe_right
                                                              trivial_post
                                                              FStar_Syntax_Syntax.as_arg
                                                             in
                                                          [uu____2810]  in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          wp uu____2809
                                                         in
                                                      uu____2804
                                                        FStar_Pervasives_Native.None
                                                        r
                                                       in
                                                    let uu____2843 =
                                                      FStar_Syntax_Syntax.mk_Total'
                                                        fml
                                                        (FStar_Pervasives_Native.Some
                                                           FStar_Syntax_Syntax.U_zero)
                                                       in
                                                    FStar_Syntax_Util.arrow
                                                      bs1 uu____2843))
                                      | uu____2846 -> failwith "Impossible!"
                                       in
                                    let uu____2848 =
                                      let uu____2851 =
                                        FStar_All.pipe_right k1
                                          (FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta;
                                             FStar_TypeChecker_Env.Eager_unfolding]
                                             env)
                                         in
                                      FStar_All.pipe_right uu____2851
                                        (FStar_Syntax_Subst.close_univ_vars
                                           stronger_us)
                                       in
                                    (stronger_us, stronger_t, uu____2848))))))))
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
              (let uu____2887 =
                 let uu____2892 =
                   FStar_Syntax_Subst.univ_var_opening
                     act.FStar_Syntax_Syntax.action_univs
                    in
                 match uu____2892 with
                 | (usubst,us) ->
                     let uu____2915 =
                       FStar_TypeChecker_Env.push_univ_vars env us  in
                     let uu____2916 =
                       let uu___365_2917 = act  in
                       let uu____2918 =
                         FStar_Syntax_Subst.subst usubst
                           act.FStar_Syntax_Syntax.action_defn
                          in
                       let uu____2919 =
                         FStar_Syntax_Subst.subst usubst
                           act.FStar_Syntax_Syntax.action_typ
                          in
                       {
                         FStar_Syntax_Syntax.action_name =
                           (uu___365_2917.FStar_Syntax_Syntax.action_name);
                         FStar_Syntax_Syntax.action_unqualified_name =
                           (uu___365_2917.FStar_Syntax_Syntax.action_unqualified_name);
                         FStar_Syntax_Syntax.action_univs = us;
                         FStar_Syntax_Syntax.action_params =
                           (uu___365_2917.FStar_Syntax_Syntax.action_params);
                         FStar_Syntax_Syntax.action_defn = uu____2918;
                         FStar_Syntax_Syntax.action_typ = uu____2919
                       }  in
                     (uu____2915, uu____2916)
                  in
               match uu____2887 with
               | (env1,act1) ->
                   let act_typ =
                     let uu____2923 =
                       let uu____2924 =
                         FStar_Syntax_Subst.compress
                           act1.FStar_Syntax_Syntax.action_typ
                          in
                       uu____2924.FStar_Syntax_Syntax.n  in
                     match uu____2923 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                         let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
                         let uu____2950 =
                           FStar_Ident.lid_equals
                             ct.FStar_Syntax_Syntax.effect_name
                             ed.FStar_Syntax_Syntax.mname
                            in
                         if uu____2950
                         then
                           let repr_ts =
                             let uu____2954 = repr  in
                             match uu____2954 with
                             | (us,t,uu____2969) -> (us, t)  in
                           let repr1 =
                             let uu____2987 =
                               FStar_TypeChecker_Env.inst_tscheme_with
                                 repr_ts ct.FStar_Syntax_Syntax.comp_univs
                                in
                             FStar_All.pipe_right uu____2987
                               FStar_Pervasives_Native.snd
                              in
                           let c1 =
                             let uu____2999 =
                               let uu____3000 =
                                 let uu____3005 =
                                   let uu____3006 =
                                     FStar_Syntax_Syntax.as_arg
                                       ct.FStar_Syntax_Syntax.result_typ
                                      in
                                   uu____3006 ::
                                     (ct.FStar_Syntax_Syntax.effect_args)
                                    in
                                 FStar_Syntax_Syntax.mk_Tm_app repr1
                                   uu____3005
                                  in
                               uu____3000 FStar_Pervasives_Native.None r  in
                             FStar_All.pipe_right uu____2999
                               FStar_Syntax_Syntax.mk_Total
                              in
                           FStar_Syntax_Util.arrow bs c1
                         else act1.FStar_Syntax_Syntax.action_typ
                     | uu____3027 -> act1.FStar_Syntax_Syntax.action_typ  in
                   let uu____3028 =
                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                       act_typ
                      in
                   (match uu____3028 with
                    | (act_typ1,uu____3036,g_t) ->
                        let uu____3038 =
                          let uu____3045 =
                            let uu___389_3046 =
                              FStar_TypeChecker_Env.set_expected_typ env1
                                act_typ1
                               in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___389_3046.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___389_3046.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___389_3046.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___389_3046.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___389_3046.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___389_3046.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___389_3046.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___389_3046.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___389_3046.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___389_3046.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___389_3046.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp = false;
                              FStar_TypeChecker_Env.effects =
                                (uu___389_3046.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___389_3046.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___389_3046.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___389_3046.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___389_3046.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___389_3046.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___389_3046.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___389_3046.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax =
                                (uu___389_3046.FStar_TypeChecker_Env.lax);
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___389_3046.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___389_3046.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___389_3046.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___389_3046.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___389_3046.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___389_3046.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___389_3046.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___389_3046.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___389_3046.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___389_3046.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___389_3046.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___389_3046.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___389_3046.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___389_3046.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___389_3046.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___389_3046.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___389_3046.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___389_3046.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___389_3046.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___389_3046.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___389_3046.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___389_3046.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___389_3046.FStar_TypeChecker_Env.strict_args_tab)
                            }  in
                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                            uu____3045 act1.FStar_Syntax_Syntax.action_defn
                           in
                        (match uu____3038 with
                         | (act_defn,uu____3049,g_d) ->
                             ((let uu____3052 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env1)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____3052
                               then
                                 let uu____3057 =
                                   FStar_Syntax_Print.term_to_string act_defn
                                    in
                                 let uu____3059 =
                                   FStar_Syntax_Print.term_to_string act_typ1
                                    in
                                 FStar_Util.print2
                                   "Typechecked action definition: %s and action type: %s\n"
                                   uu____3057 uu____3059
                               else ());
                              (let uu____3064 =
                                 let act_typ2 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Beta] env1
                                     act_typ1
                                    in
                                 let uu____3072 =
                                   let uu____3073 =
                                     FStar_Syntax_Subst.compress act_typ2  in
                                   uu____3073.FStar_Syntax_Syntax.n  in
                                 match uu____3072 with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                     let bs1 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     let env2 =
                                       FStar_TypeChecker_Env.push_binders
                                         env1 bs1
                                        in
                                     let uu____3106 =
                                       FStar_Syntax_Util.type_u ()  in
                                     (match uu____3106 with
                                      | (t,u) ->
                                          let uu____3119 =
                                            FStar_TypeChecker_Util.new_implicit_var
                                              "" r env2 t
                                             in
                                          (match uu____3119 with
                                           | (a_tm,uu____3140,g_tm) ->
                                               let uu____3154 =
                                                 fresh_repr r env2 u a_tm  in
                                               (match uu____3154 with
                                                | (repr1,g) ->
                                                    let uu____3167 =
                                                      let uu____3170 =
                                                        let uu____3173 =
                                                          let uu____3176 =
                                                            FStar_TypeChecker_Env.new_u_univ
                                                              ()
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____3176
                                                            (fun _3179  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _3179)
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total'
                                                          repr1 uu____3173
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____3170
                                                       in
                                                    let uu____3180 =
                                                      FStar_TypeChecker_Env.conj_guard
                                                        g g_tm
                                                       in
                                                    (uu____3167, uu____3180))))
                                 | uu____3183 ->
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                         "") r
                                  in
                               match uu____3064 with
                               | (k,g_k) ->
                                   ((let uu____3199 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other
                                            "LayeredEffects")
                                        in
                                     if uu____3199
                                     then
                                       let uu____3204 =
                                         FStar_Syntax_Print.term_to_string k
                                          in
                                       FStar_Util.print1
                                         "Expected action type: %s\n"
                                         uu____3204
                                     else ());
                                    (let g =
                                       FStar_TypeChecker_Rel.teq env1
                                         act_typ1 k
                                        in
                                     FStar_List.iter
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1) [g_t; g_d; g_k; g];
                                     (let uu____3212 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____3212
                                      then
                                        let uu____3217 =
                                          FStar_Syntax_Print.term_to_string k
                                           in
                                        FStar_Util.print1
                                          "Expected action type after unification: %s\n"
                                          uu____3217
                                      else ());
                                     (let act_typ2 =
                                        let repr_args t =
                                          let uu____3241 =
                                            let uu____3242 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____3242.FStar_Syntax_Syntax.n
                                             in
                                          match uu____3241 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (head1,a::is) ->
                                              let uu____3294 =
                                                let uu____3295 =
                                                  FStar_Syntax_Subst.compress
                                                    head1
                                                   in
                                                uu____3295.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____3294 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (uu____3304,us) ->
                                                   (us,
                                                     (FStar_Pervasives_Native.fst
                                                        a), is)
                                               | uu____3314 ->
                                                   failwith "Impossible!")
                                          | uu____3322 ->
                                              failwith "Impossible!"
                                           in
                                        let k1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Env.Beta] env1
                                            k
                                           in
                                        let uu____3331 =
                                          let uu____3332 =
                                            FStar_Syntax_Subst.compress k1
                                             in
                                          uu____3332.FStar_Syntax_Syntax.n
                                           in
                                        match uu____3331 with
                                        | FStar_Syntax_Syntax.Tm_arrow 
                                            (bs,c) ->
                                            let uu____3357 =
                                              FStar_Syntax_Subst.open_comp bs
                                                c
                                               in
                                            (match uu____3357 with
                                             | (bs1,c1) ->
                                                 let uu____3364 =
                                                   repr_args
                                                     (FStar_Syntax_Util.comp_result
                                                        c1)
                                                    in
                                                 (match uu____3364 with
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
                                                      let uu____3375 =
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          ct
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____3375))
                                        | uu____3378 ->
                                            failwith "Impossible!"
                                         in
                                      (let uu____3381 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____3381
                                       then
                                         let uu____3386 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ2
                                            in
                                         FStar_Util.print1
                                           "Action type after injecting it into the monad: %s\n"
                                           uu____3386
                                       else ());
                                      (let act2 =
                                         if
                                           act1.FStar_Syntax_Syntax.action_univs
                                             = []
                                         then
                                           let uu____3395 =
                                             FStar_TypeChecker_Util.generalize_universes
                                               env1 act_defn
                                              in
                                           match uu____3395 with
                                           | (us,act_defn1) ->
                                               let uu___459_3406 = act1  in
                                               let uu____3407 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   us act_typ2
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___459_3406.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___459_3406.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = us;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___459_3406.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = act_defn1;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = uu____3407
                                               }
                                         else
                                           (let uu___461_3410 = act1  in
                                            let uu____3411 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                act1.FStar_Syntax_Syntax.action_univs
                                                act_defn
                                               in
                                            let uu____3412 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                act1.FStar_Syntax_Syntax.action_univs
                                                act_typ2
                                               in
                                            {
                                              FStar_Syntax_Syntax.action_name
                                                =
                                                (uu___461_3410.FStar_Syntax_Syntax.action_name);
                                              FStar_Syntax_Syntax.action_unqualified_name
                                                =
                                                (uu___461_3410.FStar_Syntax_Syntax.action_unqualified_name);
                                              FStar_Syntax_Syntax.action_univs
                                                =
                                                (uu___461_3410.FStar_Syntax_Syntax.action_univs);
                                              FStar_Syntax_Syntax.action_params
                                                =
                                                (uu___461_3410.FStar_Syntax_Syntax.action_params);
                                              FStar_Syntax_Syntax.action_defn
                                                = uu____3411;
                                              FStar_Syntax_Syntax.action_typ
                                                = uu____3412
                                            })
                                          in
                                       act2)))))))))
               in
            let fst1 uu____3432 =
              match uu____3432 with | (a,uu____3448,uu____3449) -> a  in
            let snd1 uu____3481 =
              match uu____3481 with | (uu____3496,b,uu____3498) -> b  in
            let thd uu____3530 =
              match uu____3530 with | (uu____3545,uu____3546,c) -> c  in
            let uu___479_3560 = ed  in
            let uu____3561 =
              FStar_All.pipe_right
                ((fst1 stronger_repr), (snd1 stronger_repr))
                (fun _3570  -> FStar_Pervasives_Native.Some _3570)
               in
            let uu____3571 =
              FStar_List.map (tc_action env0) ed.FStar_Syntax_Syntax.actions
               in
            {
              FStar_Syntax_Syntax.is_layered =
                (uu___479_3560.FStar_Syntax_Syntax.is_layered);
              FStar_Syntax_Syntax.cattributes =
                (uu___479_3560.FStar_Syntax_Syntax.cattributes);
              FStar_Syntax_Syntax.mname =
                (uu___479_3560.FStar_Syntax_Syntax.mname);
              FStar_Syntax_Syntax.univs =
                (uu___479_3560.FStar_Syntax_Syntax.univs);
              FStar_Syntax_Syntax.binders =
                (uu___479_3560.FStar_Syntax_Syntax.binders);
              FStar_Syntax_Syntax.signature =
                ((fst1 signature), (snd1 signature));
              FStar_Syntax_Syntax.ret_wp =
                ((fst1 return_repr), (thd return_repr));
              FStar_Syntax_Syntax.bind_wp =
                ((fst1 bind_repr), (thd bind_repr));
              FStar_Syntax_Syntax.stronger =
                ((fst1 stronger_repr), (thd stronger_repr));
              FStar_Syntax_Syntax.match_wps =
                (uu___479_3560.FStar_Syntax_Syntax.match_wps);
              FStar_Syntax_Syntax.trivial =
                (uu___479_3560.FStar_Syntax_Syntax.trivial);
              FStar_Syntax_Syntax.repr = ((fst1 repr), (snd1 repr));
              FStar_Syntax_Syntax.return_repr =
                ((fst1 return_repr), (snd1 return_repr));
              FStar_Syntax_Syntax.bind_repr =
                ((fst1 bind_repr), (snd1 bind_repr));
              FStar_Syntax_Syntax.stronger_repr = uu____3561;
              FStar_Syntax_Syntax.actions = uu____3571;
              FStar_Syntax_Syntax.eff_attrs =
                (uu___479_3560.FStar_Syntax_Syntax.eff_attrs)
            }))))))
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____3614 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____3614
       then
         let uu____3619 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____3619
       else ());
      (let uu____3624 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____3624 with
       | (us,lift) ->
           let r = lift.FStar_Syntax_Syntax.pos  in
           (if (FStar_List.length us) <> Prims.int_zero
            then
              (let uu____3658 =
                 let uu____3660 = FStar_Syntax_Print.sub_eff_to_string sub1
                    in
                 Prims.op_Hat
                   "Unexpected number of universes in typechecking %s"
                   uu____3660
                  in
               failwith uu____3658)
            else ();
            (let uu____3665 =
               FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env0 lift  in
             match uu____3665 with
             | (lift1,lc,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env0 g;
                  (let lift_ty =
                     FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                       (FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Beta] env0)
                      in
                   (let uu____3682 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                        (FStar_Options.Other "LayeredEffects")
                       in
                    if uu____3682
                    then
                      let uu____3687 =
                        FStar_Syntax_Print.term_to_string lift1  in
                      let uu____3689 =
                        FStar_Syntax_Print.term_to_string lift_ty  in
                      FStar_Util.print2
                        "Typechecked lift: %s and lift_ty: %s\n" uu____3687
                        uu____3689
                    else ());
                   (let uu____3694 =
                      let uu____3701 =
                        let uu____3706 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____3706
                          (fun uu____3723  ->
                             match uu____3723 with
                             | (t,u) ->
                                 let uu____3734 =
                                   let uu____3735 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t
                                      in
                                   FStar_All.pipe_right uu____3735
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____3734, u))
                         in
                      match uu____3701 with
                      | (a,u_a) ->
                          let uu____3745 =
                            let uu____3752 =
                              FStar_TypeChecker_Env.lookup_effect_lid env0
                                sub1.FStar_Syntax_Syntax.source
                               in
                            monad_signature env0
                              sub1.FStar_Syntax_Syntax.source uu____3752
                             in
                          (match uu____3745 with
                           | (a',wp_sort_a') ->
                               let src_wp_sort_a =
                                 let uu____3766 =
                                   let uu____3769 =
                                     let uu____3770 =
                                       let uu____3777 =
                                         let uu____3780 =
                                           FStar_All.pipe_right a
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_All.pipe_right uu____3780
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       (a', uu____3777)  in
                                     FStar_Syntax_Syntax.NT uu____3770  in
                                   [uu____3769]  in
                                 FStar_Syntax_Subst.subst uu____3766
                                   wp_sort_a'
                                  in
                               let wp =
                                 let uu____3800 =
                                   FStar_Syntax_Syntax.gen_bv "wp"
                                     FStar_Pervasives_Native.None
                                     src_wp_sort_a
                                    in
                                 FStar_All.pipe_right uu____3800
                                   FStar_Syntax_Syntax.mk_binder
                                  in
                               let rest_bs =
                                 let uu____3817 =
                                   let uu____3818 =
                                     FStar_Syntax_Subst.compress lift_ty  in
                                   uu____3818.FStar_Syntax_Syntax.n  in
                                 match uu____3817 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____3830) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (3))
                                     ->
                                     let uu____3858 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____3858 with
                                      | (a'1,uu____3868)::(wp',uu____3870)::bs1
                                          ->
                                          let uu____3900 =
                                            FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 Prims.int_one) bs1
                                             in
                                          (match uu____3900 with
                                           | (bs2,uu____3943) ->
                                               let substs =
                                                 let uu____3979 =
                                                   let uu____3980 =
                                                     let uu____3987 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a)
                                                        in
                                                     (a'1, uu____3987)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____3980
                                                    in
                                                 let uu____3994 =
                                                   let uu____3997 =
                                                     let uu____3998 =
                                                       let uu____4005 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              wp)
                                                          in
                                                       (wp', uu____4005)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____3998
                                                      in
                                                   [uu____3997]  in
                                                 uu____3979 :: uu____3994  in
                                               FStar_Syntax_Subst.subst_binders
                                                 substs bs2)
                                      | uu____4012 -> failwith "Impossible!")
                                 | uu____4022 ->
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_UnexpectedEffect,
                                         "") r
                                  in
                               let f =
                                 let f_sort =
                                   let uu____4043 =
                                     let uu____4052 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_Syntax_Syntax.t_unit
                                        in
                                     [uu____4052]  in
                                   let uu____4071 =
                                     let uu____4074 =
                                       let uu____4075 =
                                         let uu____4078 =
                                           FStar_All.pipe_right a
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_All.pipe_right uu____4078
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       let uu____4089 =
                                         let uu____4100 =
                                           let uu____4109 =
                                             let uu____4110 =
                                               FStar_All.pipe_right wp
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____4110
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           FStar_All.pipe_right uu____4109
                                             FStar_Syntax_Syntax.as_arg
                                            in
                                         [uu____4100]  in
                                       {
                                         FStar_Syntax_Syntax.comp_univs =
                                           [u_a];
                                         FStar_Syntax_Syntax.effect_name =
                                           (sub1.FStar_Syntax_Syntax.source);
                                         FStar_Syntax_Syntax.result_typ =
                                           uu____4075;
                                         FStar_Syntax_Syntax.effect_args =
                                           uu____4089;
                                         FStar_Syntax_Syntax.flags = []
                                       }  in
                                     FStar_Syntax_Syntax.mk_Comp uu____4074
                                      in
                                   FStar_Syntax_Util.arrow uu____4043
                                     uu____4071
                                    in
                                 let uu____4143 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None f_sort
                                    in
                                 FStar_All.pipe_right uu____4143
                                   FStar_Syntax_Syntax.mk_binder
                                  in
                               let bs = a :: wp ::
                                 (FStar_List.append rest_bs [f])  in
                               let uu____4190 =
                                 let uu____4195 =
                                   FStar_TypeChecker_Env.push_binders env0 bs
                                    in
                                 let uu____4196 =
                                   let uu____4197 =
                                     FStar_All.pipe_right a
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____4197
                                     FStar_Syntax_Syntax.bv_to_name
                                    in
                                 FStar_TypeChecker_Util.fresh_layered_effect_repr_en
                                   uu____4195 r
                                   sub1.FStar_Syntax_Syntax.target u_a
                                   uu____4196
                                  in
                               (match uu____4190 with
                                | (repr,g_repr) ->
                                    let uu____4214 =
                                      let uu____4217 =
                                        let uu____4220 =
                                          let uu____4223 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_All.pipe_right uu____4223
                                            (fun _4226  ->
                                               FStar_Pervasives_Native.Some
                                                 _4226)
                                           in
                                        FStar_Syntax_Syntax.mk_Total' repr
                                          uu____4220
                                         in
                                      FStar_Syntax_Util.arrow bs uu____4217
                                       in
                                    (uu____4214, g_repr)))
                       in
                    match uu____3694 with
                    | (k,g_k) ->
                        ((let uu____4236 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____4236
                          then
                            let uu____4241 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print1 "Before unification k: %s\n"
                              uu____4241
                          else ());
                         (let g1 = FStar_TypeChecker_Rel.teq env0 lift_ty k
                             in
                          FStar_TypeChecker_Rel.force_trivial_guard env0 g_k;
                          FStar_TypeChecker_Rel.force_trivial_guard env0 g1;
                          (let uu____4250 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffects")
                              in
                           if uu____4250
                           then
                             let uu____4255 =
                               FStar_Syntax_Print.term_to_string k  in
                             FStar_Util.print1 "After unification k: %s\n"
                               uu____4255
                           else ());
                          (let uu____4260 =
                             FStar_TypeChecker_Util.generalize_universes env0
                               lift1
                              in
                           match uu____4260 with
                           | (us1,lift2) ->
                               let lift_wp =
                                 let uu____4274 =
                                   let uu____4275 =
                                     let uu____4280 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env0 us1
                                        in
                                     FStar_TypeChecker_Normalize.remove_uvar_solutions
                                       uu____4280
                                      in
                                   FStar_All.pipe_right k uu____4275  in
                                 FStar_All.pipe_right uu____4274
                                   (FStar_Syntax_Subst.close_univ_vars us1)
                                  in
                               let sub2 =
                                 let uu___550_4284 = sub1  in
                                 {
                                   FStar_Syntax_Syntax.source =
                                     (uu___550_4284.FStar_Syntax_Syntax.source);
                                   FStar_Syntax_Syntax.target =
                                     (uu___550_4284.FStar_Syntax_Syntax.target);
                                   FStar_Syntax_Syntax.lift_wp =
                                     (FStar_Pervasives_Native.Some
                                        (us1, lift_wp));
                                   FStar_Syntax_Syntax.lift =
                                     (FStar_Pervasives_Native.Some
                                        (us1, lift2))
                                 }  in
                               ((let uu____4294 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env0)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____4294
                                 then
                                   let uu____4299 =
                                     FStar_Syntax_Print.sub_eff_to_string
                                       sub2
                                      in
                                   FStar_Util.print1 "Final sub_effect: %s\n"
                                     uu____4299
                                 else ());
                                sub2))))))))))
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      (let uu____4316 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "ED")
          in
       if uu____4316
       then
         let uu____4321 = FStar_Syntax_Print.eff_decl_to_string false ed  in
         FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____4321
       else ());
      (let uu____4327 =
         let uu____4332 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____4332 with
         | (ed_univs_subst,ed_univs) ->
             let bs =
               let uu____4356 =
                 FStar_Syntax_Subst.subst_binders ed_univs_subst
                   ed.FStar_Syntax_Syntax.binders
                  in
               FStar_Syntax_Subst.open_binders uu____4356  in
             let uu____4357 =
               let uu____4364 =
                 FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
               FStar_TypeChecker_TcTerm.tc_tparams uu____4364 bs  in
             (match uu____4357 with
              | (bs1,uu____4370,uu____4371) ->
                  let uu____4372 =
                    let tmp_t =
                      let uu____4382 =
                        let uu____4385 =
                          FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                            (fun _4390  -> FStar_Pervasives_Native.Some _4390)
                           in
                        FStar_Syntax_Syntax.mk_Total'
                          FStar_Syntax_Syntax.t_unit uu____4385
                         in
                      FStar_Syntax_Util.arrow bs1 uu____4382  in
                    let uu____4391 =
                      FStar_TypeChecker_Util.generalize_universes env0 tmp_t
                       in
                    match uu____4391 with
                    | (us,tmp_t1) ->
                        let uu____4408 =
                          let uu____4409 =
                            let uu____4410 =
                              FStar_All.pipe_right tmp_t1
                                FStar_Syntax_Util.arrow_formals
                               in
                            FStar_All.pipe_right uu____4410
                              FStar_Pervasives_Native.fst
                             in
                          FStar_All.pipe_right uu____4409
                            FStar_Syntax_Subst.close_binders
                           in
                        (us, uu____4408)
                     in
                  (match uu____4372 with
                   | (us,bs2) ->
                       (match ed_univs with
                        | [] -> (us, bs2)
                        | uu____4479 ->
                            let uu____4482 =
                              ((FStar_List.length ed_univs) =
                                 (FStar_List.length us))
                                &&
                                (FStar_List.forall2
                                   (fun u1  ->
                                      fun u2  ->
                                        let uu____4489 =
                                          FStar_Syntax_Syntax.order_univ_name
                                            u1 u2
                                           in
                                        uu____4489 = Prims.int_zero) ed_univs
                                   us)
                               in
                            if uu____4482
                            then (us, bs2)
                            else
                              (let uu____4500 =
                                 let uu____4506 =
                                   let uu____4508 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length ed_univs)
                                      in
                                   let uu____4510 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length us)
                                      in
                                   FStar_Util.format3
                                     "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                     uu____4508 uu____4510
                                    in
                                 (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                   uu____4506)
                                  in
                               let uu____4514 =
                                 FStar_Ident.range_of_lid
                                   ed.FStar_Syntax_Syntax.mname
                                  in
                               FStar_Errors.raise_error uu____4500 uu____4514))))
          in
       match uu____4327 with
       | (us,bs) ->
           let ed1 =
             let uu___582_4522 = ed  in
             {
               FStar_Syntax_Syntax.is_layered =
                 (uu___582_4522.FStar_Syntax_Syntax.is_layered);
               FStar_Syntax_Syntax.cattributes =
                 (uu___582_4522.FStar_Syntax_Syntax.cattributes);
               FStar_Syntax_Syntax.mname =
                 (uu___582_4522.FStar_Syntax_Syntax.mname);
               FStar_Syntax_Syntax.univs = us;
               FStar_Syntax_Syntax.binders = bs;
               FStar_Syntax_Syntax.signature =
                 (uu___582_4522.FStar_Syntax_Syntax.signature);
               FStar_Syntax_Syntax.ret_wp =
                 (uu___582_4522.FStar_Syntax_Syntax.ret_wp);
               FStar_Syntax_Syntax.bind_wp =
                 (uu___582_4522.FStar_Syntax_Syntax.bind_wp);
               FStar_Syntax_Syntax.stronger =
                 (uu___582_4522.FStar_Syntax_Syntax.stronger);
               FStar_Syntax_Syntax.match_wps =
                 (uu___582_4522.FStar_Syntax_Syntax.match_wps);
               FStar_Syntax_Syntax.trivial =
                 (uu___582_4522.FStar_Syntax_Syntax.trivial);
               FStar_Syntax_Syntax.repr =
                 (uu___582_4522.FStar_Syntax_Syntax.repr);
               FStar_Syntax_Syntax.return_repr =
                 (uu___582_4522.FStar_Syntax_Syntax.return_repr);
               FStar_Syntax_Syntax.bind_repr =
                 (uu___582_4522.FStar_Syntax_Syntax.bind_repr);
               FStar_Syntax_Syntax.stronger_repr =
                 (uu___582_4522.FStar_Syntax_Syntax.stronger_repr);
               FStar_Syntax_Syntax.actions =
                 (uu___582_4522.FStar_Syntax_Syntax.actions);
               FStar_Syntax_Syntax.eff_attrs =
                 (uu___582_4522.FStar_Syntax_Syntax.eff_attrs)
             }  in
           let uu____4523 = FStar_Syntax_Subst.univ_var_opening us  in
           (match uu____4523 with
            | (ed_univs_subst,ed_univs) ->
                let uu____4542 =
                  let uu____4547 =
                    FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                  FStar_Syntax_Subst.open_binders' uu____4547  in
                (match uu____4542 with
                 | (ed_bs,ed_bs_subst) ->
                     let ed2 =
                       let op uu____4568 =
                         match uu____4568 with
                         | (us1,t) ->
                             let t1 =
                               let uu____4588 =
                                 FStar_Syntax_Subst.shift_subst
                                   ((FStar_List.length ed_bs) +
                                      (FStar_List.length us1)) ed_univs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____4588 t  in
                             let uu____4597 =
                               let uu____4598 =
                                 FStar_Syntax_Subst.shift_subst
                                   (FStar_List.length us1) ed_bs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____4598 t1  in
                             (us1, uu____4597)
                          in
                       let uu___596_4603 = ed1  in
                       let uu____4604 = op ed1.FStar_Syntax_Syntax.signature
                          in
                       let uu____4605 = op ed1.FStar_Syntax_Syntax.ret_wp  in
                       let uu____4606 = op ed1.FStar_Syntax_Syntax.bind_wp
                          in
                       let uu____4607 = op ed1.FStar_Syntax_Syntax.stronger
                          in
                       let uu____4608 =
                         FStar_Syntax_Util.map_match_wps op
                           ed1.FStar_Syntax_Syntax.match_wps
                          in
                       let uu____4613 =
                         FStar_Util.map_opt ed1.FStar_Syntax_Syntax.trivial
                           op
                          in
                       let uu____4616 = op ed1.FStar_Syntax_Syntax.repr  in
                       let uu____4617 =
                         op ed1.FStar_Syntax_Syntax.return_repr  in
                       let uu____4618 = op ed1.FStar_Syntax_Syntax.bind_repr
                          in
                       let uu____4619 =
                         FStar_List.map
                           (fun a  ->
                              let uu___599_4627 = a  in
                              let uu____4628 =
                                let uu____4629 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_defn))
                                   in
                                FStar_Pervasives_Native.snd uu____4629  in
                              let uu____4640 =
                                let uu____4641 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_typ))
                                   in
                                FStar_Pervasives_Native.snd uu____4641  in
                              {
                                FStar_Syntax_Syntax.action_name =
                                  (uu___599_4627.FStar_Syntax_Syntax.action_name);
                                FStar_Syntax_Syntax.action_unqualified_name =
                                  (uu___599_4627.FStar_Syntax_Syntax.action_unqualified_name);
                                FStar_Syntax_Syntax.action_univs =
                                  (uu___599_4627.FStar_Syntax_Syntax.action_univs);
                                FStar_Syntax_Syntax.action_params =
                                  (uu___599_4627.FStar_Syntax_Syntax.action_params);
                                FStar_Syntax_Syntax.action_defn = uu____4628;
                                FStar_Syntax_Syntax.action_typ = uu____4640
                              }) ed1.FStar_Syntax_Syntax.actions
                          in
                       {
                         FStar_Syntax_Syntax.is_layered =
                           (uu___596_4603.FStar_Syntax_Syntax.is_layered);
                         FStar_Syntax_Syntax.cattributes =
                           (uu___596_4603.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.mname =
                           (uu___596_4603.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.univs =
                           (uu___596_4603.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___596_4603.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature = uu____4604;
                         FStar_Syntax_Syntax.ret_wp = uu____4605;
                         FStar_Syntax_Syntax.bind_wp = uu____4606;
                         FStar_Syntax_Syntax.stronger = uu____4607;
                         FStar_Syntax_Syntax.match_wps = uu____4608;
                         FStar_Syntax_Syntax.trivial = uu____4613;
                         FStar_Syntax_Syntax.repr = uu____4616;
                         FStar_Syntax_Syntax.return_repr = uu____4617;
                         FStar_Syntax_Syntax.bind_repr = uu____4618;
                         FStar_Syntax_Syntax.stronger_repr =
                           FStar_Pervasives_Native.None;
                         FStar_Syntax_Syntax.actions = uu____4619;
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___596_4603.FStar_Syntax_Syntax.eff_attrs)
                       }  in
                     ((let uu____4653 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env0)
                           (FStar_Options.Other "ED")
                          in
                       if uu____4653
                       then
                         let uu____4658 =
                           FStar_Syntax_Print.eff_decl_to_string false ed2
                            in
                         FStar_Util.print1
                           "After typechecking binders eff_decl: \n\t%s\n"
                           uu____4658
                       else ());
                      (let env =
                         let uu____4665 =
                           FStar_TypeChecker_Env.push_univ_vars env0 ed_univs
                            in
                         FStar_TypeChecker_Env.push_binders uu____4665 ed_bs
                          in
                       let check_and_gen' comb n1 env_opt uu____4700 k =
                         match uu____4700 with
                         | (us1,t) ->
                             let env1 =
                               if FStar_Util.is_some env_opt
                               then
                                 FStar_All.pipe_right env_opt FStar_Util.must
                               else env  in
                             let uu____4720 =
                               FStar_Syntax_Subst.open_univ_vars us1 t  in
                             (match uu____4720 with
                              | (us2,t1) ->
                                  let t2 =
                                    match k with
                                    | FStar_Pervasives_Native.Some k1 ->
                                        let uu____4729 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env1 us2
                                           in
                                        tc_check_trivial_guard uu____4729 t1
                                          k1
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____4730 =
                                          let uu____4737 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            uu____4737 t1
                                           in
                                        (match uu____4730 with
                                         | (t2,uu____4739,g) ->
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env1 g;
                                              t2))
                                     in
                                  let uu____4742 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env1 t2
                                     in
                                  (match uu____4742 with
                                   | (g_us,t3) ->
                                       (if (FStar_List.length g_us) <> n1
                                        then
                                          (let error =
                                             let uu____4758 =
                                               FStar_Util.string_of_int n1
                                                in
                                             let uu____4760 =
                                               let uu____4762 =
                                                 FStar_All.pipe_right g_us
                                                   FStar_List.length
                                                  in
                                               FStar_All.pipe_right
                                                 uu____4762
                                                 FStar_Util.string_of_int
                                                in
                                             FStar_Util.format4
                                               "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                               (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                               comb uu____4758 uu____4760
                                              in
                                           FStar_Errors.raise_error
                                             (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                               error)
                                             t3.FStar_Syntax_Syntax.pos)
                                        else ();
                                        (match us2 with
                                         | [] -> (g_us, t3)
                                         | uu____4777 ->
                                             let uu____4778 =
                                               ((FStar_List.length us2) =
                                                  (FStar_List.length g_us))
                                                 &&
                                                 (FStar_List.forall2
                                                    (fun u1  ->
                                                       fun u2  ->
                                                         let uu____4785 =
                                                           FStar_Syntax_Syntax.order_univ_name
                                                             u1 u2
                                                            in
                                                         uu____4785 =
                                                           Prims.int_zero)
                                                    us2 g_us)
                                                in
                                             if uu____4778
                                             then (g_us, t3)
                                             else
                                               (let uu____4796 =
                                                  let uu____4802 =
                                                    let uu____4804 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           us2)
                                                       in
                                                    let uu____4806 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           g_us)
                                                       in
                                                    FStar_Util.format4
                                                      "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                      (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      comb uu____4804
                                                      uu____4806
                                                     in
                                                  (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                    uu____4802)
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4796
                                                  t3.FStar_Syntax_Syntax.pos)))))
                          in
                       let signature =
                         check_and_gen' "signature" Prims.int_one
                           FStar_Pervasives_Native.None
                           ed2.FStar_Syntax_Syntax.signature
                           FStar_Pervasives_Native.None
                          in
                       (let uu____4814 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env0)
                            (FStar_Options.Other "ED")
                           in
                        if uu____4814
                        then
                          let uu____4819 =
                            FStar_Syntax_Print.tscheme_to_string signature
                             in
                          FStar_Util.print1 "Typechecked signature: %s\n"
                            uu____4819
                        else ());
                       (let fresh_a_and_wp uu____4835 =
                          let fail1 t =
                            let uu____4848 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env ed2.FStar_Syntax_Syntax.mname t
                               in
                            FStar_Errors.raise_error uu____4848
                              (FStar_Pervasives_Native.snd
                                 ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                             in
                          let uu____4864 =
                            FStar_TypeChecker_Env.inst_tscheme signature  in
                          match uu____4864 with
                          | (uu____4875,signature1) ->
                              let uu____4877 =
                                let uu____4878 =
                                  FStar_Syntax_Subst.compress signature1  in
                                uu____4878.FStar_Syntax_Syntax.n  in
                              (match uu____4877 with
                               | FStar_Syntax_Syntax.Tm_arrow
                                   (bs1,uu____4888) ->
                                   let bs2 =
                                     FStar_Syntax_Subst.open_binders bs1  in
                                   (match bs2 with
                                    | (a,uu____4917)::(wp,uu____4919)::[] ->
                                        (a, (wp.FStar_Syntax_Syntax.sort))
                                    | uu____4948 -> fail1 signature1)
                               | uu____4949 -> fail1 signature1)
                           in
                        let log_combinator s ts =
                          let uu____4963 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "ED")
                             in
                          if uu____4963
                          then
                            let uu____4968 =
                              FStar_Syntax_Print.tscheme_to_string ts  in
                            FStar_Util.print3 "Typechecked %s:%s = %s\n"
                              (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                              s uu____4968
                          else ()  in
                        let ret_wp =
                          let uu____4974 = fresh_a_and_wp ()  in
                          match uu____4974 with
                          | (a,wp_sort) ->
                              let k =
                                let uu____4990 =
                                  let uu____4999 =
                                    FStar_Syntax_Syntax.mk_binder a  in
                                  let uu____5006 =
                                    let uu____5015 =
                                      let uu____5022 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      FStar_Syntax_Syntax.null_binder
                                        uu____5022
                                       in
                                    [uu____5015]  in
                                  uu____4999 :: uu____5006  in
                                let uu____5041 =
                                  FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                FStar_Syntax_Util.arrow uu____4990 uu____5041
                                 in
                              check_and_gen' "ret_wp" Prims.int_one
                                FStar_Pervasives_Native.None
                                ed2.FStar_Syntax_Syntax.ret_wp
                                (FStar_Pervasives_Native.Some k)
                           in
                        log_combinator "ret_wp" ret_wp;
                        (let bind_wp =
                           let uu____5049 = fresh_a_and_wp ()  in
                           match uu____5049 with
                           | (a,wp_sort_a) ->
                               let uu____5062 = fresh_a_and_wp ()  in
                               (match uu____5062 with
                                | (b,wp_sort_b) ->
                                    let wp_sort_a_b =
                                      let uu____5078 =
                                        let uu____5087 =
                                          let uu____5094 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____5094
                                           in
                                        [uu____5087]  in
                                      let uu____5107 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____5078
                                        uu____5107
                                       in
                                    let k =
                                      let uu____5113 =
                                        let uu____5122 =
                                          FStar_Syntax_Syntax.null_binder
                                            FStar_Syntax_Syntax.t_range
                                           in
                                        let uu____5129 =
                                          let uu____5138 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____5145 =
                                            let uu____5154 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____5161 =
                                              let uu____5170 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              let uu____5177 =
                                                let uu____5186 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a_b
                                                   in
                                                [uu____5186]  in
                                              uu____5170 :: uu____5177  in
                                            uu____5154 :: uu____5161  in
                                          uu____5138 :: uu____5145  in
                                        uu____5122 :: uu____5129  in
                                      let uu____5229 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____5113
                                        uu____5229
                                       in
                                    check_and_gen' "bind_wp"
                                      (Prims.of_int (2))
                                      FStar_Pervasives_Native.None
                                      ed2.FStar_Syntax_Syntax.bind_wp
                                      (FStar_Pervasives_Native.Some k))
                            in
                         log_combinator "bind_wp" bind_wp;
                         (let stronger =
                            let uu____5237 = fresh_a_and_wp ()  in
                            match uu____5237 with
                            | (a,wp_sort_a) ->
                                let uu____5250 = FStar_Syntax_Util.type_u ()
                                   in
                                (match uu____5250 with
                                 | (t,uu____5256) ->
                                     let k =
                                       let uu____5260 =
                                         let uu____5269 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____5276 =
                                           let uu____5285 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____5292 =
                                             let uu____5301 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____5301]  in
                                           uu____5285 :: uu____5292  in
                                         uu____5269 :: uu____5276  in
                                       let uu____5332 =
                                         FStar_Syntax_Syntax.mk_Total t  in
                                       FStar_Syntax_Util.arrow uu____5260
                                         uu____5332
                                        in
                                     check_and_gen' "stronger" Prims.int_one
                                       FStar_Pervasives_Native.None
                                       ed2.FStar_Syntax_Syntax.stronger
                                       (FStar_Pervasives_Native.Some k))
                             in
                          log_combinator "stronger" stronger;
                          (let match_wps =
                             let uu____5344 =
                               FStar_Syntax_Util.get_match_with_close_wps
                                 ed2.FStar_Syntax_Syntax.match_wps
                                in
                             match uu____5344 with
                             | (if_then_else1,ite_wp,close_wp) ->
                                 let if_then_else2 =
                                   let uu____5359 = fresh_a_and_wp ()  in
                                   match uu____5359 with
                                   | (a,wp_sort_a) ->
                                       let p =
                                         let uu____5373 =
                                           let uu____5376 =
                                             FStar_Ident.range_of_lid
                                               ed2.FStar_Syntax_Syntax.mname
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____5376
                                            in
                                         let uu____5377 =
                                           let uu____5378 =
                                             FStar_Syntax_Util.type_u ()  in
                                           FStar_All.pipe_right uu____5378
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____5373 uu____5377
                                          in
                                       let k =
                                         let uu____5390 =
                                           let uu____5399 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____5406 =
                                             let uu____5415 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 p
                                                in
                                             let uu____5422 =
                                               let uu____5431 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               let uu____5438 =
                                                 let uu____5447 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____5447]  in
                                               uu____5431 :: uu____5438  in
                                             uu____5415 :: uu____5422  in
                                           uu____5399 :: uu____5406  in
                                         let uu____5484 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a
                                            in
                                         FStar_Syntax_Util.arrow uu____5390
                                           uu____5484
                                          in
                                       check_and_gen' "if_then_else"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         if_then_else1
                                         (FStar_Pervasives_Native.Some k)
                                    in
                                 (log_combinator "if_then_else" if_then_else2;
                                  (let ite_wp1 =
                                     let uu____5492 = fresh_a_and_wp ()  in
                                     match uu____5492 with
                                     | (a,wp_sort_a) ->
                                         let k =
                                           let uu____5508 =
                                             let uu____5517 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____5524 =
                                               let uu____5533 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____5533]  in
                                             uu____5517 :: uu____5524  in
                                           let uu____5558 =
                                             FStar_Syntax_Syntax.mk_Total
                                               wp_sort_a
                                              in
                                           FStar_Syntax_Util.arrow uu____5508
                                             uu____5558
                                            in
                                         check_and_gen' "ite_wp"
                                           Prims.int_one
                                           FStar_Pervasives_Native.None
                                           ite_wp
                                           (FStar_Pervasives_Native.Some k)
                                      in
                                   log_combinator "ite_wp" ite_wp1;
                                   (let close_wp1 =
                                      let uu____5566 = fresh_a_and_wp ()  in
                                      match uu____5566 with
                                      | (a,wp_sort_a) ->
                                          let b =
                                            let uu____5580 =
                                              let uu____5583 =
                                                FStar_Ident.range_of_lid
                                                  ed2.FStar_Syntax_Syntax.mname
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____5583
                                               in
                                            let uu____5584 =
                                              let uu____5585 =
                                                FStar_Syntax_Util.type_u ()
                                                 in
                                              FStar_All.pipe_right uu____5585
                                                FStar_Pervasives_Native.fst
                                               in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____5580 uu____5584
                                             in
                                          let wp_sort_b_a =
                                            let uu____5597 =
                                              let uu____5606 =
                                                let uu____5613 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    b
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____5613
                                                 in
                                              [uu____5606]  in
                                            let uu____5626 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____5597 uu____5626
                                             in
                                          let k =
                                            let uu____5632 =
                                              let uu____5641 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____5648 =
                                                let uu____5657 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    b
                                                   in
                                                let uu____5664 =
                                                  let uu____5673 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_b_a
                                                     in
                                                  [uu____5673]  in
                                                uu____5657 :: uu____5664  in
                                              uu____5641 :: uu____5648  in
                                            let uu____5704 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____5632 uu____5704
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
                             let uu____5714 = fresh_a_and_wp ()  in
                             match uu____5714 with
                             | (a,wp_sort_a) ->
                                 let uu____5729 = FStar_Syntax_Util.type_u ()
                                    in
                                 (match uu____5729 with
                                  | (t,uu____5737) ->
                                      let k =
                                        let uu____5741 =
                                          let uu____5750 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____5757 =
                                            let uu____5766 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_sort_a
                                               in
                                            [uu____5766]  in
                                          uu____5750 :: uu____5757  in
                                        let uu____5791 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____5741
                                          uu____5791
                                         in
                                      let trivial =
                                        let uu____5795 =
                                          FStar_All.pipe_right
                                            ed2.FStar_Syntax_Syntax.trivial
                                            FStar_Util.must
                                           in
                                        check_and_gen' "trivial"
                                          Prims.int_one
                                          FStar_Pervasives_Native.None
                                          uu____5795
                                          (FStar_Pervasives_Native.Some k)
                                         in
                                      (log_combinator "trivial" trivial;
                                       FStar_Pervasives_Native.Some trivial))
                              in
                           let uu____5810 =
                             let uu____5821 =
                               let uu____5822 =
                                 FStar_Syntax_Subst.compress
                                   (FStar_Pervasives_Native.snd
                                      ed2.FStar_Syntax_Syntax.repr)
                                  in
                               uu____5822.FStar_Syntax_Syntax.n  in
                             match uu____5821 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____5841 ->
                                 let repr =
                                   let uu____5843 = fresh_a_and_wp ()  in
                                   match uu____5843 with
                                   | (a,wp_sort_a) ->
                                       let uu____5856 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____5856 with
                                        | (t,uu____5862) ->
                                            let k =
                                              let uu____5866 =
                                                let uu____5875 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____5882 =
                                                  let uu____5891 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a
                                                     in
                                                  [uu____5891]  in
                                                uu____5875 :: uu____5882  in
                                              let uu____5916 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____5866 uu____5916
                                               in
                                            check_and_gen' "repr"
                                              Prims.int_one
                                              FStar_Pervasives_Native.None
                                              ed2.FStar_Syntax_Syntax.repr
                                              (FStar_Pervasives_Native.Some k))
                                    in
                                 (log_combinator "repr" repr;
                                  (let mk_repr' t wp =
                                     let uu____5936 =
                                       FStar_TypeChecker_Env.inst_tscheme
                                         repr
                                        in
                                     match uu____5936 with
                                     | (uu____5943,repr1) ->
                                         let repr2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.EraseUniverses;
                                             FStar_TypeChecker_Env.AllowUnboundUniverses]
                                             env repr1
                                            in
                                         let uu____5946 =
                                           let uu____5953 =
                                             let uu____5954 =
                                               let uu____5971 =
                                                 let uu____5982 =
                                                   FStar_All.pipe_right t
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____5999 =
                                                   let uu____6010 =
                                                     FStar_All.pipe_right wp
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____6010]  in
                                                 uu____5982 :: uu____5999  in
                                               (repr2, uu____5971)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5954
                                              in
                                           FStar_Syntax_Syntax.mk uu____5953
                                            in
                                         uu____5946
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                      in
                                   let mk_repr a wp =
                                     let uu____6076 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     mk_repr' uu____6076 wp  in
                                   let destruct_repr t =
                                     let uu____6091 =
                                       let uu____6092 =
                                         FStar_Syntax_Subst.compress t  in
                                       uu____6092.FStar_Syntax_Syntax.n  in
                                     match uu____6091 with
                                     | FStar_Syntax_Syntax.Tm_app
                                         (uu____6103,(t1,uu____6105)::
                                          (wp,uu____6107)::[])
                                         -> (t1, wp)
                                     | uu____6166 ->
                                         failwith "Unexpected repr type"
                                      in
                                   let return_repr =
                                     let uu____6177 = fresh_a_and_wp ()  in
                                     match uu____6177 with
                                     | (a,uu____6185) ->
                                         let x_a =
                                           let uu____6191 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x_a"
                                             FStar_Pervasives_Native.None
                                             uu____6191
                                            in
                                         let res =
                                           let wp =
                                             let uu____6199 =
                                               let uu____6204 =
                                                 let uu____6205 =
                                                   FStar_TypeChecker_Env.inst_tscheme
                                                     ret_wp
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____6205
                                                   FStar_Pervasives_Native.snd
                                                  in
                                               let uu____6214 =
                                                 let uu____6215 =
                                                   let uu____6224 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6224
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____6233 =
                                                   let uu____6244 =
                                                     let uu____6253 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         x_a
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____6253
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____6244]  in
                                                 uu____6215 :: uu____6233  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____6204 uu____6214
                                                in
                                             uu____6199
                                               FStar_Pervasives_Native.None
                                               FStar_Range.dummyRange
                                              in
                                           mk_repr a wp  in
                                         let k =
                                           let uu____6289 =
                                             let uu____6298 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____6305 =
                                               let uu____6314 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   x_a
                                                  in
                                               [uu____6314]  in
                                             uu____6298 :: uu____6305  in
                                           let uu____6339 =
                                             FStar_Syntax_Syntax.mk_Total res
                                              in
                                           FStar_Syntax_Util.arrow uu____6289
                                             uu____6339
                                            in
                                         let uu____6342 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env k
                                            in
                                         (match uu____6342 with
                                          | (k1,uu____6350,uu____6351) ->
                                              let env1 =
                                                let uu____6355 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env
                                                    (FStar_Pervasives_Native.snd
                                                       ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____6355
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
                                        let uu____6366 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            FStar_Parser_Const.range_0
                                            FStar_Syntax_Syntax.delta_constant
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_All.pipe_right uu____6366
                                          FStar_Syntax_Syntax.fv_to_tm
                                         in
                                      let uu____6367 = fresh_a_and_wp ()  in
                                      match uu____6367 with
                                      | (a,wp_sort_a) ->
                                          let uu____6380 = fresh_a_and_wp ()
                                             in
                                          (match uu____6380 with
                                           | (b,wp_sort_b) ->
                                               let wp_sort_a_b =
                                                 let uu____6396 =
                                                   let uu____6405 =
                                                     let uu____6412 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____6412
                                                      in
                                                   [uu____6405]  in
                                                 let uu____6425 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     wp_sort_b
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____6396 uu____6425
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
                                                 let uu____6433 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     a
                                                    in
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "x_a"
                                                   FStar_Pervasives_Native.None
                                                   uu____6433
                                                  in
                                               let wp_g_x =
                                                 let uu____6438 =
                                                   let uu____6443 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       wp_g
                                                      in
                                                   let uu____6444 =
                                                     let uu____6445 =
                                                       let uu____6454 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x_a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____6454
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____6445]  in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     uu____6443 uu____6444
                                                    in
                                                 uu____6438
                                                   FStar_Pervasives_Native.None
                                                   FStar_Range.dummyRange
                                                  in
                                               let res =
                                                 let wp =
                                                   let uu____6485 =
                                                     let uu____6490 =
                                                       let uu____6491 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           bind_wp
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____6491
                                                         FStar_Pervasives_Native.snd
                                                        in
                                                     let uu____6500 =
                                                       let uu____6501 =
                                                         let uu____6504 =
                                                           let uu____6507 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               a
                                                              in
                                                           let uu____6508 =
                                                             let uu____6511 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 b
                                                                in
                                                             let uu____6512 =
                                                               let uu____6515
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_f
                                                                  in
                                                               let uu____6516
                                                                 =
                                                                 let uu____6519
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g
                                                                    in
                                                                 [uu____6519]
                                                                  in
                                                               uu____6515 ::
                                                                 uu____6516
                                                                in
                                                             uu____6511 ::
                                                               uu____6512
                                                              in
                                                           uu____6507 ::
                                                             uu____6508
                                                            in
                                                         r :: uu____6504  in
                                                       FStar_List.map
                                                         FStar_Syntax_Syntax.as_arg
                                                         uu____6501
                                                        in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____6490 uu____6500
                                                      in
                                                   uu____6485
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 mk_repr b wp  in
                                               let maybe_range_arg =
                                                 let uu____6537 =
                                                   FStar_Util.for_some
                                                     (FStar_Syntax_Util.attr_eq
                                                        FStar_Syntax_Util.dm4f_bind_range_attr)
                                                     ed2.FStar_Syntax_Syntax.eff_attrs
                                                    in
                                                 if uu____6537
                                                 then
                                                   let uu____6548 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       FStar_Syntax_Syntax.t_range
                                                      in
                                                   let uu____6555 =
                                                     let uu____6564 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         FStar_Syntax_Syntax.t_range
                                                        in
                                                     [uu____6564]  in
                                                   uu____6548 :: uu____6555
                                                 else []  in
                                               let k =
                                                 let uu____6600 =
                                                   let uu____6609 =
                                                     let uu____6618 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6625 =
                                                       let uu____6634 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           b
                                                          in
                                                       [uu____6634]  in
                                                     uu____6618 :: uu____6625
                                                      in
                                                   let uu____6659 =
                                                     let uu____6668 =
                                                       let uu____6677 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           wp_f
                                                          in
                                                       let uu____6684 =
                                                         let uu____6693 =
                                                           let uu____6700 =
                                                             let uu____6701 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp_f
                                                                in
                                                             mk_repr a
                                                               uu____6701
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____6700
                                                            in
                                                         let uu____6702 =
                                                           let uu____6711 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               wp_g
                                                              in
                                                           let uu____6718 =
                                                             let uu____6727 =
                                                               let uu____6734
                                                                 =
                                                                 let uu____6735
                                                                   =
                                                                   let uu____6744
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                   [uu____6744]
                                                                    in
                                                                 let uu____6763
                                                                   =
                                                                   let uu____6766
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                   FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____6766
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   uu____6735
                                                                   uu____6763
                                                                  in
                                                               FStar_Syntax_Syntax.null_binder
                                                                 uu____6734
                                                                in
                                                             [uu____6727]  in
                                                           uu____6711 ::
                                                             uu____6718
                                                            in
                                                         uu____6693 ::
                                                           uu____6702
                                                          in
                                                       uu____6677 ::
                                                         uu____6684
                                                        in
                                                     FStar_List.append
                                                       maybe_range_arg
                                                       uu____6668
                                                      in
                                                   FStar_List.append
                                                     uu____6609 uu____6659
                                                    in
                                                 let uu____6811 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     res
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____6600 uu____6811
                                                  in
                                               let uu____6814 =
                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                   env k
                                                  in
                                               (match uu____6814 with
                                                | (k1,uu____6822,uu____6823)
                                                    ->
                                                    let env1 =
                                                      FStar_TypeChecker_Env.set_range
                                                        env
                                                        (FStar_Pervasives_Native.snd
                                                           ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                       in
                                                    let env2 =
                                                      FStar_All.pipe_right
                                                        (let uu___797_6835 =
                                                           env1  in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.instantiate_imp);
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             = true;
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.nbe);
                                                           FStar_TypeChecker_Env.strict_args_tab
                                                             =
                                                             (uu___797_6835.FStar_TypeChecker_Env.strict_args_tab)
                                                         })
                                                        (fun _6837  ->
                                                           FStar_Pervasives_Native.Some
                                                             _6837)
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
                                         (let uu____6864 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env, act)
                                            else
                                              (let uu____6878 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____6878 with
                                               | (usubst,uvs) ->
                                                   let uu____6901 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env uvs
                                                      in
                                                   let uu____6902 =
                                                     let uu___810_6903 = act
                                                        in
                                                     let uu____6904 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____6905 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___810_6903.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___810_6903.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___810_6903.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____6904;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____6905
                                                     }  in
                                                   (uu____6901, uu____6902))
                                             in
                                          match uu____6864 with
                                          | (env1,act1) ->
                                              let act_typ =
                                                let uu____6909 =
                                                  let uu____6910 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  uu____6910.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____6909 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs1,c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c
                                                       in
                                                    let uu____6936 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname
                                                       in
                                                    if uu____6936
                                                    then
                                                      let uu____6939 =
                                                        let uu____6942 =
                                                          let uu____6943 =
                                                            let uu____6944 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____6944
                                                             in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____6943
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____6942
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____6939
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____6967 ->
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              let uu____6968 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env1 act_typ
                                                 in
                                              (match uu____6968 with
                                               | (act_typ1,uu____6976,g_t) ->
                                                   let env' =
                                                     let uu___827_6979 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env1 act_typ1
                                                        in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_sig
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.gamma_sig);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.attrtab
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.attrtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.phase1
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.phase1);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.uvar_subtyping
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.uvar_subtyping);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.fv_delta_depths
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.fv_delta_depths);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.postprocess
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.postprocess);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.nbe
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.nbe);
                                                       FStar_TypeChecker_Env.strict_args_tab
                                                         =
                                                         (uu___827_6979.FStar_TypeChecker_Env.strict_args_tab)
                                                     }  in
                                                   ((let uu____6982 =
                                                       FStar_TypeChecker_Env.debug
                                                         env1
                                                         (FStar_Options.Other
                                                            "ED")
                                                        in
                                                     if uu____6982
                                                     then
                                                       let uu____6986 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name
                                                          in
                                                       let uu____6988 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____6990 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1
                                                          in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____6986
                                                         uu____6988
                                                         uu____6990
                                                     else ());
                                                    (let uu____6995 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     match uu____6995 with
                                                     | (act_defn,uu____7003,g_a)
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
                                                         let uu____7007 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2
                                                              in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs1,c) ->
                                                               let uu____7043
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs1 c
                                                                  in
                                                               (match uu____7043
                                                                with
                                                                | (bs2,uu____7055)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____7062
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____7062
                                                                     in
                                                                    let uu____7065
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____7065
                                                                    with
                                                                    | 
                                                                    (k1,uu____7079,g)
                                                                    ->
                                                                    (k1, g)))
                                                           | uu____7083 ->
                                                               let uu____7084
                                                                 =
                                                                 let uu____7090
                                                                   =
                                                                   let uu____7092
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                   let uu____7094
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____7092
                                                                    uu____7094
                                                                    in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____7090)
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____7084
                                                                 act_defn1.FStar_Syntax_Syntax.pos
                                                            in
                                                         (match uu____7007
                                                          with
                                                          | (expected_k,g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env1
                                                                  act_typ2
                                                                  expected_k
                                                                 in
                                                              ((let uu____7112
                                                                  =
                                                                  let uu____7113
                                                                    =
                                                                    let uu____7114
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____7114
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____7113
                                                                   in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env1
                                                                  uu____7112);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____7116
                                                                    =
                                                                    let uu____7117
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____7117.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____7116
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____7142
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____7142
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____7149
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____7149
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____7169
                                                                    =
                                                                    let uu____7170
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____7170]
                                                                     in
                                                                    let uu____7171
                                                                    =
                                                                    let uu____7182
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____7182]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____7169;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____7171;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____7207
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____7207))
                                                                  | uu____7210
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                   in
                                                                let uu____7212
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
                                                                    let uu____7234
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____7234))
                                                                   in
                                                                match uu____7212
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
                                                                    let uu___877_7253
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___877_7253.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___877_7253.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___877_7253.FStar_Syntax_Syntax.action_params);
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
                           match uu____5810 with
                           | (repr,return_repr,bind_repr,actions) ->
                               let cl ts =
                                 let ts1 =
                                   FStar_Syntax_Subst.close_tscheme ed_bs ts
                                    in
                                 let ed_univs_closing =
                                   FStar_Syntax_Subst.univ_var_closing
                                     ed_univs
                                    in
                                 let uu____7278 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length ed_bs)
                                     ed_univs_closing
                                    in
                                 FStar_Syntax_Subst.subst_tscheme uu____7278
                                   ts1
                                  in
                               let ed3 =
                                 let uu___889_7288 = ed2  in
                                 let uu____7289 = cl signature  in
                                 let uu____7290 = cl ret_wp  in
                                 let uu____7291 = cl bind_wp  in
                                 let uu____7292 = cl stronger  in
                                 let uu____7293 =
                                   FStar_Syntax_Util.map_match_wps cl
                                     match_wps
                                    in
                                 let uu____7298 =
                                   FStar_Util.map_opt trivial cl  in
                                 let uu____7301 = cl repr  in
                                 let uu____7302 = cl return_repr  in
                                 let uu____7303 = cl bind_repr  in
                                 let uu____7304 =
                                   FStar_List.map
                                     (fun a  ->
                                        let uu___892_7312 = a  in
                                        let uu____7313 =
                                          let uu____7314 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_All.pipe_right uu____7314
                                            FStar_Pervasives_Native.snd
                                           in
                                        let uu____7339 =
                                          let uu____7340 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_All.pipe_right uu____7340
                                            FStar_Pervasives_Native.snd
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            (uu___892_7312.FStar_Syntax_Syntax.action_name);
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (uu___892_7312.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (uu___892_7312.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (uu___892_7312.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____7313;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____7339
                                        }) actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.is_layered =
                                     (uu___889_7288.FStar_Syntax_Syntax.is_layered);
                                   FStar_Syntax_Syntax.cattributes =
                                     (uu___889_7288.FStar_Syntax_Syntax.cattributes);
                                   FStar_Syntax_Syntax.mname =
                                     (uu___889_7288.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.univs =
                                     (uu___889_7288.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders =
                                     (uu___889_7288.FStar_Syntax_Syntax.binders);
                                   FStar_Syntax_Syntax.signature = uu____7289;
                                   FStar_Syntax_Syntax.ret_wp = uu____7290;
                                   FStar_Syntax_Syntax.bind_wp = uu____7291;
                                   FStar_Syntax_Syntax.stronger = uu____7292;
                                   FStar_Syntax_Syntax.match_wps = uu____7293;
                                   FStar_Syntax_Syntax.trivial = uu____7298;
                                   FStar_Syntax_Syntax.repr = uu____7301;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____7302;
                                   FStar_Syntax_Syntax.bind_repr = uu____7303;
                                   FStar_Syntax_Syntax.stronger_repr =
                                     FStar_Pervasives_Native.None;
                                   FStar_Syntax_Syntax.actions = uu____7304;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (uu___889_7288.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               ((let uu____7366 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____7366
                                 then
                                   let uu____7371 =
                                     FStar_Syntax_Print.eff_decl_to_string
                                       false ed3
                                      in
                                   FStar_Util.print1
                                     "Typechecked effect declaration:\n\t%s\n"
                                     uu____7371
                                 else ());
                                ed3))))))))))
  
let tc_lex_t :
  'Auu____7388 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____7388 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____7423 = FStar_List.hd ses  in
            uu____7423.FStar_Syntax_Syntax.sigrng  in
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
           | uu____7428 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____7434,[],t,uu____7436,uu____7437);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____7439;
               FStar_Syntax_Syntax.sigattrs = uu____7440;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____7442,_t_top,_lex_t_top,_7476,uu____7445);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____7447;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____7448;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____7450,_t_cons,_lex_t_cons,_7484,uu____7453);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____7455;
                 FStar_Syntax_Syntax.sigattrs = uu____7456;_}::[]
               when
               ((_7476 = Prims.int_zero) && (_7484 = Prims.int_zero)) &&
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
                 let uu____7509 =
                   let uu____7516 =
                     let uu____7517 =
                       let uu____7524 =
                         let uu____7527 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____7527
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____7524, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____7517  in
                   FStar_Syntax_Syntax.mk uu____7516  in
                 uu____7509 FStar_Pervasives_Native.None r1  in
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
                   let uu____7542 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7542
                    in
                 let hd1 =
                   let uu____7544 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7544
                    in
                 let tl1 =
                   let uu____7546 =
                     let uu____7547 =
                       let uu____7554 =
                         let uu____7555 =
                           let uu____7562 =
                             let uu____7565 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____7565
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____7562, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____7555  in
                       FStar_Syntax_Syntax.mk uu____7554  in
                     uu____7547 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7546
                    in
                 let res =
                   let uu____7571 =
                     let uu____7578 =
                       let uu____7579 =
                         let uu____7586 =
                           let uu____7589 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____7589
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____7586,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____7579  in
                     FStar_Syntax_Syntax.mk uu____7578  in
                   uu____7571 FStar_Pervasives_Native.None r2  in
                 let uu____7592 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____7592
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
               let uu____7631 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____7631;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____7636 ->
               let err_msg =
                 let uu____7641 =
                   let uu____7643 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____7643  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____7641
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
    fun uu____7668  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____7668 with
          | (uvs,t) ->
              let uu____7681 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____7681 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____7693 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____7693 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____7711 =
                        let uu____7714 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____7714
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____7711)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7737 =
          let uu____7738 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7738 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7737 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7763 =
          let uu____7764 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7764 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7763 r
  
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
          (let uu____7813 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____7813
           then
             let uu____7816 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____7816
           else ());
          (let uu____7821 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____7821 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____7852 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____7852 FStar_List.flatten  in
               ((let uu____7866 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____7869 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____7869)
                    in
                 if uu____7866
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
                           let uu____7885 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____7895,uu____7896,uu____7897,uu____7898,uu____7899)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____7908 -> failwith "Impossible!"  in
                           match uu____7885 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Inductive type "
                                      (Prims.op_Hat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____7927 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____7937,uu____7938,ty_lid,uu____7940,uu____7941)
                               -> (data_lid, ty_lid)
                           | uu____7948 -> failwith "Impossible"  in
                         match uu____7927 with
                         | (data_lid,ty_lid) ->
                             let uu____7956 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____7959 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____7959)
                                in
                             if uu____7956
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Exception "
                                      (Prims.op_Hat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____7973 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____7978,uu____7979,uu____7980,uu____7981,uu____7982)
                         -> lid
                     | uu____7991 -> failwith "Impossible"  in
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
                   let uu____8009 =
                     (((FStar_List.length tcs) = Prims.int_zero) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____8009
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
          let pop1 uu____8084 =
            let uu____8085 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___1064_8095  ->
               match () with
               | () ->
                   let uu____8102 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____8102 (fun r  -> pop1 (); r)) ()
          with | uu___1063_8133 -> (pop1 (); FStar_Exn.raise uu___1063_8133)
  
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
      | uu____8449 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____8507 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____8507 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____8532 .
    'Auu____8532 FStar_Pervasives_Native.option -> 'Auu____8532 Prims.list
  =
  fun uu___0_8541  ->
    match uu___0_8541 with
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
            let uu____8621 = collect1 tl1  in
            (match uu____8621 with
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
        | ((e,n1)::uu____8859,[]) ->
            FStar_Pervasives_Native.Some (e, n1, Prims.int_zero)
        | ([],(e,n1)::uu____8915) ->
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
          let uu____9125 =
            let uu____9127 = FStar_Options.ide ()  in
            Prims.op_Negation uu____9127  in
          if uu____9125
          then
            let uu____9130 =
              let uu____9135 = FStar_TypeChecker_Env.dsenv env  in
              let uu____9136 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____9135 uu____9136  in
            (match uu____9130 with
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
                              let uu____9169 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____9170 =
                                let uu____9176 =
                                  let uu____9178 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____9180 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____9178 uu____9180
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____9176)
                                 in
                              FStar_Errors.log_issue uu____9169 uu____9170
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____9187 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____9188 =
                                   let uu____9194 =
                                     let uu____9196 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____9196
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____9194)
                                    in
                                 FStar_Errors.log_issue uu____9187 uu____9188)
                              else ())
                         else ())))
          else ()
      | uu____9206 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____9251 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____9279 ->
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
             let uu____9339 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____9339
             then
               let ses1 =
                 let uu____9347 =
                   let uu____9348 =
                     let uu____9349 =
                       tc_inductive
                         (let uu___1196_9358 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1196_9358.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1196_9358.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1196_9358.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1196_9358.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1196_9358.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1196_9358.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1196_9358.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1196_9358.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1196_9358.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1196_9358.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1196_9358.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1196_9358.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1196_9358.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1196_9358.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1196_9358.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1196_9358.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1196_9358.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1196_9358.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1196_9358.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1196_9358.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1196_9358.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___1196_9358.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1196_9358.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1196_9358.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1196_9358.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1196_9358.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1196_9358.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1196_9358.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1196_9358.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1196_9358.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1196_9358.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1196_9358.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1196_9358.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1196_9358.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1196_9358.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1196_9358.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1196_9358.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1196_9358.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1196_9358.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1196_9358.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1196_9358.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1196_9358.FStar_TypeChecker_Env.strict_args_tab)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____9349
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____9348
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____9347
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____9372 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____9372
                 then
                   let uu____9377 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1200_9381 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1200_9381.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1200_9381.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1200_9381.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1200_9381.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____9377
                 else ());
                ses1)
             else ses  in
           let uu____9391 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____9391 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___1207_9415 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1207_9415.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1207_9415.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1207_9415.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1207_9415.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____9427 = FStar_TypeChecker_DMFF.cps_and_elaborate env ne
              in
           (match uu____9427 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___1221_9466 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1221_9466.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1221_9466.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1221_9466.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1221_9466.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___1224_9468 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1224_9468.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1224_9468.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1224_9468.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1224_9468.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses), env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           ((let uu____9475 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "LayeredEffects")
                in
             if uu____9475
             then
               let uu____9480 = FStar_Syntax_Print.sigelt_to_string se  in
               FStar_Util.print1
                 "Starting to typecheck layered effect:\n%s\n" uu____9480
             else ());
            (let tc_fun =
               if ne.FStar_Syntax_Syntax.is_layered
               then tc_layered_eff_decl
               else tc_eff_decl  in
             let ne1 =
               let uu____9504 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env)
                  in
               if uu____9504
               then
                 let ne1 =
                   let uu____9508 =
                     let uu____9509 =
                       let uu____9510 =
                         tc_fun
                           (let uu___1234_9513 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1234_9513.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1234_9513.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1234_9513.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1234_9513.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1234_9513.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1234_9513.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1234_9513.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1234_9513.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1234_9513.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1234_9513.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1234_9513.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1234_9513.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1234_9513.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1234_9513.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1234_9513.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1234_9513.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1234_9513.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1234_9513.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1234_9513.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1234_9513.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1234_9513.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 = true;
                              FStar_TypeChecker_Env.failhard =
                                (uu___1234_9513.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1234_9513.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1234_9513.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1234_9513.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1234_9513.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1234_9513.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1234_9513.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1234_9513.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1234_9513.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1234_9513.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1234_9513.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1234_9513.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1234_9513.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1234_9513.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1234_9513.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1234_9513.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1234_9513.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1234_9513.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1234_9513.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1234_9513.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1234_9513.FStar_TypeChecker_Env.strict_args_tab)
                            }) ne
                          in
                       FStar_All.pipe_right uu____9510
                         (fun ne1  ->
                            let uu___1237_9519 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_new_effect ne1);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___1237_9519.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___1237_9519.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___1237_9519.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___1237_9519.FStar_Syntax_Syntax.sigattrs)
                            })
                        in
                     FStar_All.pipe_right uu____9509
                       (FStar_TypeChecker_Normalize.elim_uvars env)
                      in
                   FStar_All.pipe_right uu____9508
                     FStar_Syntax_Util.eff_decl_of_new_effect
                    in
                 ((let uu____9521 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "TwoPhases")
                      in
                   if uu____9521
                   then
                     let uu____9526 =
                       FStar_Syntax_Print.sigelt_to_string
                         (let uu___1241_9530 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1241_9530.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1241_9530.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1241_9530.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1241_9530.FStar_Syntax_Syntax.sigattrs)
                          })
                        in
                     FStar_Util.print1 "Effect decl after phase 1: %s\n"
                       uu____9526
                   else ());
                  ne1)
               else ne  in
             let ne2 = tc_fun env ne1  in
             let se1 =
               let uu___1246_9538 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_new_effect ne2);
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1246_9538.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1246_9538.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1246_9538.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1246_9538.FStar_Syntax_Syntax.sigattrs)
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
             ([(let uu___1255_9563 = se  in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                  FStar_Syntax_Syntax.sigrng =
                    (uu___1255_9563.FStar_Syntax_Syntax.sigrng);
                  FStar_Syntax_Syntax.sigquals =
                    (uu___1255_9563.FStar_Syntax_Syntax.sigquals);
                  FStar_Syntax_Syntax.sigmeta =
                    (uu___1255_9563.FStar_Syntax_Syntax.sigmeta);
                  FStar_Syntax_Syntax.sigattrs =
                    (uu___1255_9563.FStar_Syntax_Syntax.sigattrs)
                })], [], env0)
           else
             (let uu____9566 =
                let uu____9573 =
                  FStar_TypeChecker_Env.lookup_effect_lid env
                    sub1.FStar_Syntax_Syntax.source
                   in
                monad_signature env sub1.FStar_Syntax_Syntax.source
                  uu____9573
                 in
              match uu____9566 with
              | (a,wp_a_src) ->
                  let uu____9590 =
                    let uu____9597 =
                      FStar_TypeChecker_Env.lookup_effect_lid env
                        sub1.FStar_Syntax_Syntax.target
                       in
                    monad_signature env sub1.FStar_Syntax_Syntax.target
                      uu____9597
                     in
                  (match uu____9590 with
                   | (b,wp_b_tgt) ->
                       let wp_a_tgt =
                         let uu____9615 =
                           let uu____9618 =
                             let uu____9619 =
                               let uu____9626 =
                                 FStar_Syntax_Syntax.bv_to_name a  in
                               (b, uu____9626)  in
                             FStar_Syntax_Syntax.NT uu____9619  in
                           [uu____9618]  in
                         FStar_Syntax_Subst.subst uu____9615 wp_b_tgt  in
                       let expected_k =
                         let uu____9634 =
                           let uu____9643 = FStar_Syntax_Syntax.mk_binder a
                              in
                           let uu____9650 =
                             let uu____9659 =
                               FStar_Syntax_Syntax.null_binder wp_a_src  in
                             [uu____9659]  in
                           uu____9643 :: uu____9650  in
                         let uu____9684 =
                           FStar_Syntax_Syntax.mk_Total wp_a_tgt  in
                         FStar_Syntax_Util.arrow uu____9634 uu____9684  in
                       let repr_type eff_name a1 wp =
                         (let uu____9706 =
                            let uu____9708 =
                              FStar_TypeChecker_Env.is_reifiable_effect env
                                eff_name
                               in
                            Prims.op_Negation uu____9708  in
                          if uu____9706
                          then
                            let uu____9711 =
                              let uu____9717 =
                                FStar_Util.format1
                                  "Effect %s cannot be reified"
                                  eff_name.FStar_Ident.str
                                 in
                              (FStar_Errors.Fatal_EffectCannotBeReified,
                                uu____9717)
                               in
                            let uu____9721 =
                              FStar_TypeChecker_Env.get_range env  in
                            FStar_Errors.raise_error uu____9711 uu____9721
                          else ());
                         (let uu____9724 =
                            FStar_TypeChecker_Env.effect_decl_opt env
                              eff_name
                             in
                          match uu____9724 with
                          | FStar_Pervasives_Native.None  ->
                              failwith
                                "internal error: reifiable effect has no decl?"
                          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                              let repr =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [FStar_Syntax_Syntax.U_unknown] env ed
                                  ed.FStar_Syntax_Syntax.repr
                                 in
                              let uu____9757 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____9758 =
                                let uu____9765 =
                                  let uu____9766 =
                                    let uu____9783 =
                                      let uu____9794 =
                                        FStar_Syntax_Syntax.as_arg a1  in
                                      let uu____9803 =
                                        let uu____9814 =
                                          FStar_Syntax_Syntax.as_arg wp  in
                                        [uu____9814]  in
                                      uu____9794 :: uu____9803  in
                                    (repr, uu____9783)  in
                                  FStar_Syntax_Syntax.Tm_app uu____9766  in
                                FStar_Syntax_Syntax.mk uu____9765  in
                              uu____9758 FStar_Pervasives_Native.None
                                uu____9757)
                          in
                       let uu____9859 =
                         match ((sub1.FStar_Syntax_Syntax.lift),
                                 (sub1.FStar_Syntax_Syntax.lift_wp))
                         with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.None ) ->
                             failwith "Impossible (parser)"
                         | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp))
                             ->
                             let uu____10032 =
                               if (FStar_List.length uvs) > Prims.int_zero
                               then
                                 let uu____10043 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10043 with
                                 | (usubst,uvs1) ->
                                     let uu____10066 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env uvs1
                                        in
                                     let uu____10067 =
                                       FStar_Syntax_Subst.subst usubst
                                         lift_wp
                                        in
                                     (uu____10066, uu____10067)
                               else (env, lift_wp)  in
                             (match uu____10032 with
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
                                       let uu____10117 =
                                         FStar_Syntax_Subst.close_univ_vars
                                           uvs lift_wp2
                                          in
                                       (uvs, uu____10117))
                                     in
                                  (lift, lift_wp2))
                         | (FStar_Pervasives_Native.Some
                            (what,lift),FStar_Pervasives_Native.None ) ->
                             let uu____10188 =
                               if (FStar_List.length what) > Prims.int_zero
                               then
                                 let uu____10203 =
                                   FStar_Syntax_Subst.univ_var_opening what
                                    in
                                 match uu____10203 with
                                 | (usubst,uvs) ->
                                     let uu____10228 =
                                       FStar_Syntax_Subst.subst usubst lift
                                        in
                                     (uvs, uu____10228)
                               else ([], lift)  in
                             (match uu____10188 with
                              | (uvs,lift1) ->
                                  ((let uu____10264 =
                                      FStar_TypeChecker_Env.debug env
                                        (FStar_Options.Other "ED")
                                       in
                                    if uu____10264
                                    then
                                      let uu____10268 =
                                        FStar_Syntax_Print.term_to_string
                                          lift1
                                         in
                                      FStar_Util.print1
                                        "Lift for free : %s\n" uu____10268
                                    else ());
                                   (let dmff_env =
                                      FStar_TypeChecker_DMFF.empty env
                                        (FStar_TypeChecker_TcTerm.tc_constant
                                           env FStar_Range.dummyRange)
                                       in
                                    let uu____10274 =
                                      let uu____10281 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env uvs
                                         in
                                      FStar_TypeChecker_TcTerm.tc_term
                                        uu____10281 lift1
                                       in
                                    match uu____10274 with
                                    | (lift2,comp,uu____10306) ->
                                        let uu____10307 =
                                          FStar_TypeChecker_DMFF.star_expr
                                            dmff_env lift2
                                           in
                                        (match uu____10307 with
                                         | (uu____10336,lift_wp,lift_elab) ->
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
                                               let uu____10368 =
                                                 let uu____10379 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env lift_elab1
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____10379
                                                  in
                                               let uu____10396 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_wp1
                                                  in
                                               (uu____10368, uu____10396)
                                             else
                                               (let uu____10425 =
                                                  let uu____10436 =
                                                    let uu____10445 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift_elab1
                                                       in
                                                    (uvs, uu____10445)  in
                                                  FStar_Pervasives_Native.Some
                                                    uu____10436
                                                   in
                                                let uu____10460 =
                                                  let uu____10469 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_wp1
                                                     in
                                                  (uvs, uu____10469)  in
                                                (uu____10425, uu____10460))))))
                          in
                       (match uu____9859 with
                        | (lift,lift_wp) ->
                            let env1 =
                              let uu___1326_10543 = env  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___1326_10543.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___1326_10543.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___1326_10543.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___1326_10543.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___1326_10543.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___1326_10543.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___1326_10543.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___1326_10543.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___1326_10543.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___1326_10543.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___1326_10543.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___1326_10543.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___1326_10543.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___1326_10543.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___1326_10543.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___1326_10543.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___1326_10543.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___1326_10543.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___1326_10543.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___1326_10543.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___1326_10543.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 =
                                  (uu___1326_10543.FStar_TypeChecker_Env.phase1);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___1326_10543.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___1326_10543.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___1326_10543.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___1326_10543.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___1326_10543.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___1326_10543.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___1326_10543.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___1326_10543.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___1326_10543.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___1326_10543.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___1326_10543.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___1326_10543.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___1326_10543.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___1326_10543.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___1326_10543.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___1326_10543.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___1326_10543.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___1326_10543.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___1326_10543.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___1326_10543.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___1326_10543.FStar_TypeChecker_Env.strict_args_tab)
                              }  in
                            let lift1 =
                              match lift with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None
                              | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                  let uu____10576 =
                                    let uu____10581 =
                                      FStar_Syntax_Subst.univ_var_opening uvs
                                       in
                                    match uu____10581 with
                                    | (usubst,uvs1) ->
                                        let uu____10604 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env1 uvs1
                                           in
                                        let uu____10605 =
                                          FStar_Syntax_Subst.subst usubst
                                            lift1
                                           in
                                        (uu____10604, uu____10605)
                                     in
                                  (match uu____10576 with
                                   | (env2,lift2) ->
                                       let uu____10610 =
                                         let uu____10617 =
                                           FStar_TypeChecker_Env.lookup_effect_lid
                                             env2
                                             sub1.FStar_Syntax_Syntax.source
                                            in
                                         monad_signature env2
                                           sub1.FStar_Syntax_Syntax.source
                                           uu____10617
                                          in
                                       (match uu____10610 with
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
                                                let uu____10643 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env2
                                                   in
                                                let uu____10644 =
                                                  let uu____10651 =
                                                    let uu____10652 =
                                                      let uu____10669 =
                                                        let uu____10680 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            a_typ
                                                           in
                                                        let uu____10689 =
                                                          let uu____10700 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              wp_a_typ
                                                             in
                                                          [uu____10700]  in
                                                        uu____10680 ::
                                                          uu____10689
                                                         in
                                                      (lift_wp1, uu____10669)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10652
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10651
                                                   in
                                                uu____10644
                                                  FStar_Pervasives_Native.None
                                                  uu____10643
                                                 in
                                              repr_type
                                                sub1.FStar_Syntax_Syntax.target
                                                a_typ lift_wp_a
                                               in
                                            let expected_k1 =
                                              let uu____10748 =
                                                let uu____10757 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a1
                                                   in
                                                let uu____10764 =
                                                  let uu____10773 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      wp_a
                                                     in
                                                  let uu____10780 =
                                                    let uu____10789 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        repr_f
                                                       in
                                                    [uu____10789]  in
                                                  uu____10773 :: uu____10780
                                                   in
                                                uu____10757 :: uu____10764
                                                 in
                                              let uu____10820 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  repr_result
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____10748 uu____10820
                                               in
                                            let uu____10823 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k1
                                               in
                                            (match uu____10823 with
                                             | (expected_k2,uu____10833,uu____10834)
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
                                                      let uu____10842 =
                                                        FStar_Syntax_Subst.close_univ_vars
                                                          uvs lift3
                                                         in
                                                      (uvs, uu____10842))
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   lift3)))
                               in
                            ((let uu____10850 =
                                let uu____10852 =
                                  let uu____10854 =
                                    FStar_All.pipe_right lift_wp
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10854
                                    FStar_List.length
                                   in
                                uu____10852 <> Prims.int_one  in
                              if uu____10850
                              then
                                let uu____10877 =
                                  let uu____10883 =
                                    let uu____10885 =
                                      FStar_Syntax_Print.lid_to_string
                                        sub1.FStar_Syntax_Syntax.source
                                       in
                                    let uu____10887 =
                                      FStar_Syntax_Print.lid_to_string
                                        sub1.FStar_Syntax_Syntax.target
                                       in
                                    let uu____10889 =
                                      let uu____10891 =
                                        let uu____10893 =
                                          FStar_All.pipe_right lift_wp
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____10893
                                          FStar_List.length
                                         in
                                      FStar_All.pipe_right uu____10891
                                        FStar_Util.string_of_int
                                       in
                                    FStar_Util.format3
                                      "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                      uu____10885 uu____10887 uu____10889
                                     in
                                  (FStar_Errors.Fatal_TooManyUniverse,
                                    uu____10883)
                                   in
                                FStar_Errors.raise_error uu____10877 r
                              else ());
                             (let uu____10920 =
                                (FStar_Util.is_some lift1) &&
                                  (let uu____10923 =
                                     let uu____10925 =
                                       let uu____10928 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10928
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10925
                                       FStar_List.length
                                      in
                                   uu____10923 <> Prims.int_one)
                                 in
                              if uu____10920
                              then
                                let uu____10967 =
                                  let uu____10973 =
                                    let uu____10975 =
                                      FStar_Syntax_Print.lid_to_string
                                        sub1.FStar_Syntax_Syntax.source
                                       in
                                    let uu____10977 =
                                      FStar_Syntax_Print.lid_to_string
                                        sub1.FStar_Syntax_Syntax.target
                                       in
                                    let uu____10979 =
                                      let uu____10981 =
                                        let uu____10983 =
                                          let uu____10986 =
                                            FStar_All.pipe_right lift1
                                              FStar_Util.must
                                             in
                                          FStar_All.pipe_right uu____10986
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____10983
                                          FStar_List.length
                                         in
                                      FStar_All.pipe_right uu____10981
                                        FStar_Util.string_of_int
                                       in
                                    FStar_Util.format3
                                      "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                      uu____10975 uu____10977 uu____10979
                                     in
                                  (FStar_Errors.Fatal_TooManyUniverse,
                                    uu____10973)
                                   in
                                FStar_Errors.raise_error uu____10967 r
                              else ());
                             (let sub2 =
                                let uu___1363_11029 = sub1  in
                                {
                                  FStar_Syntax_Syntax.source =
                                    (uu___1363_11029.FStar_Syntax_Syntax.source);
                                  FStar_Syntax_Syntax.target =
                                    (uu___1363_11029.FStar_Syntax_Syntax.target);
                                  FStar_Syntax_Syntax.lift_wp =
                                    (FStar_Pervasives_Native.Some lift_wp);
                                  FStar_Syntax_Syntax.lift = lift1
                                }  in
                              let se1 =
                                let uu___1366_11031 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1366_11031.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1366_11031.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1366_11031.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1366_11031.FStar_Syntax_Syntax.sigattrs)
                                }  in
                              ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let uu____11045 =
             if (FStar_List.length uvs) = Prims.int_zero
             then (env, uvs, tps, c)
             else
               (let uu____11073 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____11073 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____11104 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____11104 c  in
                    let uu____11113 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____11113, uvs1, tps1, c1))
              in
           (match uu____11045 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____11135 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____11135 with
                 | (tps2,c2) ->
                     let uu____11152 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____11152 with
                      | (tps3,env3,us) ->
                          let uu____11172 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____11172 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____11200)::uu____11201 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____11220 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____11228 =
                                   let uu____11230 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____11230  in
                                 if uu____11228
                                 then
                                   let uu____11233 =
                                     let uu____11239 =
                                       let uu____11241 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____11243 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____11241 uu____11243
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____11239)
                                      in
                                   FStar_Errors.raise_error uu____11233 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____11251 =
                                   let uu____11252 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____11252
                                    in
                                 match uu____11251 with
                                 | (uvs2,t) ->
                                     let uu____11283 =
                                       let uu____11288 =
                                         let uu____11301 =
                                           let uu____11302 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____11302.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____11301)  in
                                       match uu____11288 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____11317,c5)) -> ([], c5)
                                       | (uu____11359,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____11398 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____11283 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               Prims.int_one
                                           then
                                             (let uu____11432 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____11432 with
                                              | (uu____11437,t1) ->
                                                  let uu____11439 =
                                                    let uu____11445 =
                                                      let uu____11447 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____11449 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____11453 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____11447
                                                        uu____11449
                                                        uu____11453
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____11445)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____11439 r)
                                           else ();
                                           (let se1 =
                                              let uu___1436_11460 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___1436_11460.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___1436_11460.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___1436_11460.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___1436_11460.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____11467,uu____11468,uu____11469) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_11474  ->
                   match uu___1_11474 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____11477 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____11483,uu____11484) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_11493  ->
                   match uu___1_11493 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____11496 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____11507 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____11507
             then
               let uu____11510 =
                 let uu____11516 =
                   let uu____11518 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____11518
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____11516)
                  in
               FStar_Errors.raise_error uu____11510 r
             else ());
            (let uu____11524 =
               let uu____11533 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____11533
               then
                 let uu____11544 =
                   tc_declare_typ
                     (let uu___1460_11547 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1460_11547.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1460_11547.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1460_11547.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1460_11547.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1460_11547.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1460_11547.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1460_11547.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1460_11547.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1460_11547.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1460_11547.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1460_11547.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1460_11547.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1460_11547.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1460_11547.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1460_11547.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1460_11547.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1460_11547.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1460_11547.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1460_11547.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1460_11547.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1460_11547.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1460_11547.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1460_11547.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1460_11547.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1460_11547.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1460_11547.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1460_11547.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1460_11547.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1460_11547.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1460_11547.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1460_11547.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1460_11547.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1460_11547.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1460_11547.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1460_11547.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1460_11547.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1460_11547.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1460_11547.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1460_11547.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1460_11547.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___1460_11547.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___1460_11547.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1460_11547.FStar_TypeChecker_Env.strict_args_tab)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____11544 with
                 | (uvs1,t1) ->
                     ((let uu____11572 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____11572
                       then
                         let uu____11577 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____11579 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____11577 uu____11579
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____11524 with
             | (uvs1,t1) ->
                 let uu____11614 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____11614 with
                  | (uvs2,t2) ->
                      ([(let uu___1473_11644 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1473_11644.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1473_11644.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1473_11644.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1473_11644.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____11649 =
             let uu____11658 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____11658
             then
               let uu____11669 =
                 tc_assume
                   (let uu___1482_11672 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1482_11672.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1482_11672.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1482_11672.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1482_11672.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1482_11672.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1482_11672.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1482_11672.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1482_11672.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1482_11672.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1482_11672.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1482_11672.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1482_11672.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1482_11672.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1482_11672.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1482_11672.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1482_11672.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1482_11672.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1482_11672.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1482_11672.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1482_11672.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1482_11672.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___1482_11672.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1482_11672.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1482_11672.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1482_11672.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1482_11672.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1482_11672.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1482_11672.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1482_11672.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1482_11672.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1482_11672.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1482_11672.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1482_11672.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1482_11672.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1482_11672.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1482_11672.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1482_11672.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1482_11672.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1482_11672.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1482_11672.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1482_11672.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1482_11672.FStar_TypeChecker_Env.strict_args_tab)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____11669 with
               | (uvs1,t1) ->
                   ((let uu____11698 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____11698
                     then
                       let uu____11703 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____11705 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____11703
                         uu____11705
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____11649 with
            | (uvs1,t1) ->
                let uu____11740 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____11740 with
                 | (uvs2,t2) ->
                     ([(let uu___1495_11770 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1495_11770.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1495_11770.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1495_11770.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1495_11770.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____11774 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____11774 with
            | (e1,c,g1) ->
                let uu____11794 =
                  let uu____11801 = FStar_TypeChecker_Common.lcomp_comp c  in
                  match uu____11801 with
                  | (c1,g_lc) ->
                      let uu____11814 =
                        let uu____11821 =
                          let uu____11824 =
                            FStar_Syntax_Util.ml_comp
                              FStar_Syntax_Syntax.t_unit r
                             in
                          FStar_Pervasives_Native.Some uu____11824  in
                        FStar_TypeChecker_TcTerm.check_expected_effect env2
                          uu____11821 (e1, c1)
                         in
                      (match uu____11814 with
                       | (e2,_x,g) ->
                           let uu____11834 =
                             FStar_TypeChecker_Env.conj_guard g_lc g  in
                           (e2, _x, uu____11834))
                   in
                (match uu____11794 with
                 | (e2,uu____11846,g) ->
                     ((let uu____11849 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____11849);
                      (let se1 =
                         let uu___1517_11851 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1517_11851.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1517_11851.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1517_11851.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1517_11851.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____11863 = FStar_Options.debug_any ()  in
             if uu____11863
             then
               let uu____11866 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____11868 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____11866
                 uu____11868
             else ());
            (let uu____11873 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____11873 with
             | (t1,uu____11891,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____11905 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____11905 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____11908 =
                              let uu____11914 =
                                let uu____11916 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____11918 =
                                  let uu____11920 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____11920
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____11916 uu____11918
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____11914)
                               in
                            FStar_Errors.raise_error uu____11908 r
                        | uu____11932 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___1538_11937 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1538_11937.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1538_11937.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1538_11937.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1538_11937.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1538_11937.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1538_11937.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1538_11937.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1538_11937.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1538_11937.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1538_11937.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1538_11937.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1538_11937.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1538_11937.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1538_11937.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1538_11937.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1538_11937.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1538_11937.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1538_11937.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1538_11937.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1538_11937.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___1538_11937.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1538_11937.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1538_11937.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1538_11937.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1538_11937.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1538_11937.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1538_11937.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1538_11937.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1538_11937.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1538_11937.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1538_11937.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1538_11937.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1538_11937.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1538_11937.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1538_11937.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1538_11937.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1538_11937.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1538_11937.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1538_11937.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1538_11937.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1538_11937.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___1538_11937.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1538_11937.FStar_TypeChecker_Env.strict_args_tab)
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
                 let uu____12005 =
                   let uu____12007 =
                     let uu____12016 = drop_logic val_q  in
                     let uu____12019 = drop_logic q'  in
                     (uu____12016, uu____12019)  in
                   match uu____12007 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____12005
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____12046 =
                      let uu____12052 =
                        let uu____12054 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____12056 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____12058 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____12054 uu____12056 uu____12058
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____12052)
                       in
                    FStar_Errors.raise_error uu____12046 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____12095 =
                   let uu____12096 = FStar_Syntax_Subst.compress def  in
                   uu____12096.FStar_Syntax_Syntax.n  in
                 match uu____12095 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____12108,uu____12109) -> binders
                 | uu____12134 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____12146;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____12251) -> val_bs1
                     | (uu____12282,[]) -> val_bs1
                     | ((body_bv,uu____12314)::bt,(val_bv,aqual)::vt) ->
                         let uu____12371 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____12395) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___1607_12409 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___1609_12412 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___1609_12412.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___1607_12409.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1607_12409.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____12371
                      in
                   let uu____12419 =
                     let uu____12426 =
                       let uu____12427 =
                         let uu____12442 = rename_binders1 def_bs val_bs  in
                         (uu____12442, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____12427  in
                     FStar_Syntax_Syntax.mk uu____12426  in
                   uu____12419 FStar_Pervasives_Native.None r1
               | uu____12461 -> typ1  in
             let uu___1615_12462 = lb  in
             let uu____12463 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___1615_12462.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1615_12462.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____12463;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1615_12462.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___1615_12462.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1615_12462.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1615_12462.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____12466 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____12521  ->
                     fun lb  ->
                       match uu____12521 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____12567 =
                             let uu____12579 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____12579 with
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
                                   | uu____12659 ->
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
                                  (let uu____12706 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____12706, quals_opt1)))
                              in
                           (match uu____12567 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____12466 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____12810 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___2_12816  ->
                                match uu___2_12816 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____12821 -> false))
                         in
                      if uu____12810
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____12834 =
                    let uu____12841 =
                      let uu____12842 =
                        let uu____12856 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____12856)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____12842  in
                    FStar_Syntax_Syntax.mk uu____12841  in
                  uu____12834 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___1658_12875 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1658_12875.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1658_12875.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1658_12875.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1658_12875.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1658_12875.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1658_12875.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1658_12875.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1658_12875.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1658_12875.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1658_12875.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1658_12875.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1658_12875.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1658_12875.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1658_12875.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1658_12875.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1658_12875.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1658_12875.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1658_12875.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1658_12875.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1658_12875.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1658_12875.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1658_12875.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1658_12875.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1658_12875.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1658_12875.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1658_12875.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1658_12875.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1658_12875.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1658_12875.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1658_12875.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1658_12875.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1658_12875.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1658_12875.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1658_12875.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1658_12875.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1658_12875.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1658_12875.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1658_12875.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1658_12875.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1658_12875.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1658_12875.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___1658_12875.FStar_TypeChecker_Env.strict_args_tab)
                  }  in
                let e1 =
                  let uu____12878 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____12878
                  then
                    let drop_lbtyp e_lax =
                      let uu____12887 =
                        let uu____12888 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____12888.FStar_Syntax_Syntax.n  in
                      match uu____12887 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____12910 =
                              let uu____12911 = FStar_Syntax_Subst.compress e
                                 in
                              uu____12911.FStar_Syntax_Syntax.n  in
                            match uu____12910 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____12915,lb1::[]),uu____12917) ->
                                let uu____12933 =
                                  let uu____12934 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____12934.FStar_Syntax_Syntax.n  in
                                (match uu____12933 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____12939 -> false)
                            | uu____12941 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___1683_12945 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___1685_12960 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___1685_12960.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___1685_12960.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___1685_12960.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___1685_12960.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___1685_12960.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___1685_12960.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___1683_12945.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___1683_12945.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____12963 -> e_lax  in
                    let uu____12964 =
                      FStar_Util.record_time
                        (fun uu____12972  ->
                           let uu____12973 =
                             let uu____12974 =
                               let uu____12975 =
                                 FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                   (let uu___1689_12984 = env'  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___1689_12984.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___1689_12984.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___1689_12984.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___1689_12984.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___1689_12984.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___1689_12984.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___1689_12984.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___1689_12984.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___1689_12984.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___1689_12984.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___1689_12984.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___1689_12984.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___1689_12984.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___1689_12984.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___1689_12984.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___1689_12984.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___1689_12984.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___1689_12984.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___1689_12984.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___1689_12984.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___1689_12984.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___1689_12984.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___1689_12984.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___1689_12984.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___1689_12984.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___1689_12984.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___1689_12984.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___1689_12984.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___1689_12984.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___1689_12984.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___1689_12984.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___1689_12984.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___1689_12984.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___1689_12984.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___1689_12984.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___1689_12984.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___1689_12984.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___1689_12984.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___1689_12984.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___1689_12984.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___1689_12984.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___1689_12984.FStar_TypeChecker_Env.strict_args_tab)
                                    }) e
                                  in
                               FStar_All.pipe_right uu____12975
                                 (fun uu____12997  ->
                                    match uu____12997 with
                                    | (e1,uu____13005,uu____13006) -> e1)
                                in
                             FStar_All.pipe_right uu____12974
                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                  env')
                              in
                           FStar_All.pipe_right uu____12973 drop_lbtyp)
                       in
                    match uu____12964 with
                    | (e1,ms) ->
                        ((let uu____13012 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TwoPhases")
                             in
                          if uu____13012
                          then
                            let uu____13017 =
                              FStar_Syntax_Print.term_to_string e1  in
                            FStar_Util.print1
                              "Let binding after phase 1: %s\n" uu____13017
                          else ());
                         (let uu____13023 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TCDeclTime")
                             in
                          if uu____13023
                          then
                            let uu____13028 = FStar_Util.string_of_int ms  in
                            FStar_Util.print1
                              "Let binding elaborated (phase 1) in %s milliseconds\n"
                              uu____13028
                          else ());
                         e1)
                  else e  in
                let uu____13035 =
                  let uu____13044 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____13044 with
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
                (match uu____13035 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___1719_13149 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___1719_13149.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1719_13149.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1719_13149.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1719_13149.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___1726_13162 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1726_13162.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1726_13162.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___1726_13162.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___1726_13162.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1726_13162.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1726_13162.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____13163 =
                       FStar_Util.record_time
                         (fun uu____13182  ->
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              env' e1)
                        in
                     (match uu____13163 with
                      | (r1,ms) ->
                          ((let uu____13210 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TCDeclTime")
                               in
                            if uu____13210
                            then
                              let uu____13215 = FStar_Util.string_of_int ms
                                 in
                              FStar_Util.print1
                                "Let binding typechecked in phase 2 in %s milliseconds\n"
                                uu____13215
                            else ());
                           (let uu____13220 =
                              match r1 with
                              | ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                                   FStar_Syntax_Syntax.pos = uu____13245;
                                   FStar_Syntax_Syntax.vars = uu____13246;_},uu____13247,g)
                                  when FStar_TypeChecker_Env.is_trivial g ->
                                  let lbs2 =
                                    let uu____13277 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.snd lbs1)
                                        (FStar_List.map rename_parameters)
                                       in
                                    ((FStar_Pervasives_Native.fst lbs1),
                                      uu____13277)
                                     in
                                  let lbs3 =
                                    let uu____13301 =
                                      match post_tau with
                                      | FStar_Pervasives_Native.Some tau ->
                                          FStar_List.map (postprocess_lb tau)
                                            (FStar_Pervasives_Native.snd lbs2)
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.snd lbs2
                                       in
                                    ((FStar_Pervasives_Native.fst lbs2),
                                      uu____13301)
                                     in
                                  let quals1 =
                                    match e2.FStar_Syntax_Syntax.n with
                                    | FStar_Syntax_Syntax.Tm_meta
                                        (uu____13324,FStar_Syntax_Syntax.Meta_desugared
                                         (FStar_Syntax_Syntax.Masked_effect
                                         ))
                                        ->
                                        FStar_Syntax_Syntax.HasMaskedEffect
                                        :: quals
                                    | uu____13329 -> quals  in
                                  ((let uu___1756_13338 = se1  in
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_let
                                           (lbs3, lids));
                                      FStar_Syntax_Syntax.sigrng =
                                        (uu___1756_13338.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals = quals1;
                                      FStar_Syntax_Syntax.sigmeta =
                                        (uu___1756_13338.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (uu___1756_13338.FStar_Syntax_Syntax.sigattrs)
                                    }), lbs3)
                              | uu____13341 ->
                                  failwith
                                    "impossible (typechecking should preserve Tm_let)"
                               in
                            match uu____13220 with
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
                                 (let uu____13397 = log env1  in
                                  if uu____13397
                                  then
                                    let uu____13400 =
                                      let uu____13402 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.snd lbs1)
                                          (FStar_List.map
                                             (fun lb  ->
                                                let should_log =
                                                  let uu____13422 =
                                                    let uu____13431 =
                                                      let uu____13432 =
                                                        let uu____13435 =
                                                          FStar_Util.right
                                                            lb.FStar_Syntax_Syntax.lbname
                                                           in
                                                        uu____13435.FStar_Syntax_Syntax.fv_name
                                                         in
                                                      uu____13432.FStar_Syntax_Syntax.v
                                                       in
                                                    FStar_TypeChecker_Env.try_lookup_val_decl
                                                      env1 uu____13431
                                                     in
                                                  match uu____13422 with
                                                  | FStar_Pervasives_Native.None
                                                       -> true
                                                  | uu____13444 -> false  in
                                                if should_log
                                                then
                                                  let uu____13456 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  let uu____13458 =
                                                    FStar_Syntax_Print.term_to_string
                                                      lb.FStar_Syntax_Syntax.lbtyp
                                                     in
                                                  FStar_Util.format2
                                                    "let %s : %s" uu____13456
                                                    uu____13458
                                                else ""))
                                         in
                                      FStar_All.pipe_right uu____13402
                                        (FStar_String.concat "\n")
                                       in
                                    FStar_Util.print1 "%s\n" uu____13400
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
      (let uu____13510 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____13510
       then
         let uu____13513 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____13513
       else ());
      (let uu____13518 = get_fail_se se  in
       match uu____13518 with
       | FStar_Pervasives_Native.Some (uu____13539,false ) when
           let uu____13556 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____13556 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___1787_13582 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___1787_13582.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___1787_13582.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___1787_13582.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___1787_13582.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___1787_13582.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___1787_13582.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___1787_13582.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___1787_13582.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___1787_13582.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___1787_13582.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___1787_13582.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___1787_13582.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___1787_13582.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___1787_13582.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___1787_13582.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___1787_13582.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___1787_13582.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___1787_13582.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___1787_13582.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___1787_13582.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___1787_13582.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___1787_13582.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___1787_13582.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___1787_13582.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___1787_13582.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___1787_13582.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___1787_13582.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___1787_13582.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___1787_13582.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___1787_13582.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___1787_13582.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___1787_13582.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___1787_13582.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___1787_13582.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___1787_13582.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___1787_13582.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___1787_13582.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___1787_13582.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___1787_13582.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___1787_13582.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___1787_13582.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___1787_13582.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___1787_13582.FStar_TypeChecker_Env.strict_args_tab)
               }
             else env1  in
           ((let uu____13587 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____13587
             then
               let uu____13590 =
                 let uu____13592 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____13592
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____13590
             else ());
            (let uu____13606 =
               FStar_Errors.catch_errors
                 (fun uu____13636  ->
                    FStar_Options.with_saved_options
                      (fun uu____13648  -> tc_decl' env' se))
                in
             match uu____13606 with
             | (errs,uu____13660) ->
                 ((let uu____13690 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____13690
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____13725 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____13725  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____13737 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____13748 =
                            let uu____13758 = check_multi_eq errnos1 actual
                               in
                            match uu____13758 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- Prims.int_one), (~- Prims.int_one),
                                  (~- Prims.int_one))
                             in
                          (match uu____13748 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____13823 =
                                   let uu____13829 =
                                     let uu____13831 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____13834 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____13837 =
                                       FStar_Util.string_of_int e  in
                                     let uu____13839 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____13841 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____13831 uu____13834 uu____13837
                                       uu____13839 uu____13841
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____13829)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____13823)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____13868 .
    'Auu____13868 ->
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
               (fun uu___3_13911  ->
                  match uu___3_13911 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____13914 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____13925) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____13933 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____13943 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____13948 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____13964 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____13990 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14016) ->
            let uu____14025 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____14025
            then
              let for_export_bundle se1 uu____14062 =
                match uu____14062 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____14101,uu____14102) ->
                         let dec =
                           let uu___1863_14112 = se1  in
                           let uu____14113 =
                             let uu____14114 =
                               let uu____14121 =
                                 let uu____14122 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____14122  in
                               (l, us, uu____14121)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____14114
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____14113;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1863_14112.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1863_14112.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1863_14112.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____14132,uu____14133,uu____14134) ->
                         let dec =
                           let uu___1874_14142 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1874_14142.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1874_14142.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1874_14142.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____14147 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____14170,uu____14171,uu____14172) ->
            let uu____14173 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____14173 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____14197 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____14197
            then
              ([(let uu___1890_14216 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___1890_14216.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___1890_14216.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___1890_14216.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____14219 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_14225  ->
                         match uu___4_14225 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____14228 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____14234 ->
                             true
                         | uu____14236 -> false))
                  in
               if uu____14219 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____14257 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____14262 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14267 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____14272 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14277 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____14295) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____14309 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____14309
            then ([], hidden)
            else
              (let dec =
                 let uu____14330 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____14330;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____14341 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____14341
            then
              let uu____14352 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1927_14366 = se  in
                        let uu____14367 =
                          let uu____14368 =
                            let uu____14375 =
                              let uu____14376 =
                                let uu____14379 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____14379.FStar_Syntax_Syntax.fv_name  in
                              uu____14376.FStar_Syntax_Syntax.v  in
                            (uu____14375, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____14368  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____14367;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1927_14366.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1927_14366.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1927_14366.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____14352, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____14402 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____14402
       then
         let uu____14405 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____14405
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____14410 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____14428 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
           uu____14445) ->
           let env1 =
             let uu___1948_14450 = env  in
             let uu____14451 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1948_14450.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1948_14450.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1948_14450.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1948_14450.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1948_14450.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1948_14450.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1948_14450.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1948_14450.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1948_14450.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1948_14450.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1948_14450.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1948_14450.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1948_14450.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1948_14450.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1948_14450.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1948_14450.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1948_14450.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1948_14450.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1948_14450.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1948_14450.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1948_14450.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1948_14450.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1948_14450.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1948_14450.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1948_14450.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1948_14450.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1948_14450.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1948_14450.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1948_14450.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1948_14450.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1948_14450.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1948_14450.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1948_14450.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1948_14450.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14451;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1948_14450.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1948_14450.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1948_14450.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1948_14450.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1948_14450.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1948_14450.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1948_14450.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1948_14450.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1948_14450.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
           let env1 =
             let uu___1948_14453 = env  in
             let uu____14454 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1948_14453.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1948_14453.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1948_14453.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1948_14453.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1948_14453.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1948_14453.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1948_14453.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1948_14453.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1948_14453.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1948_14453.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1948_14453.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1948_14453.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1948_14453.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1948_14453.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1948_14453.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1948_14453.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1948_14453.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1948_14453.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1948_14453.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1948_14453.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1948_14453.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1948_14453.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1948_14453.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1948_14453.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1948_14453.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1948_14453.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1948_14453.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1948_14453.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1948_14453.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1948_14453.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1948_14453.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1948_14453.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1948_14453.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1948_14453.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14454;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1948_14453.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1948_14453.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1948_14453.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1948_14453.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1948_14453.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1948_14453.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1948_14453.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1948_14453.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1948_14453.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions
           uu____14455) ->
           let env1 =
             let uu___1948_14458 = env  in
             let uu____14459 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1948_14458.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1948_14458.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1948_14458.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1948_14458.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1948_14458.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1948_14458.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1948_14458.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1948_14458.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1948_14458.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1948_14458.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1948_14458.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1948_14458.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1948_14458.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1948_14458.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1948_14458.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1948_14458.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1948_14458.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1948_14458.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1948_14458.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1948_14458.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1948_14458.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1948_14458.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1948_14458.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1948_14458.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1948_14458.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1948_14458.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1948_14458.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1948_14458.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1948_14458.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1948_14458.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1948_14458.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1948_14458.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1948_14458.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1948_14458.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14459;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1948_14458.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1948_14458.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1948_14458.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1948_14458.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1948_14458.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1948_14458.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1948_14458.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1948_14458.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1948_14458.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____14460) ->
           let env1 =
             let uu___1948_14465 = env  in
             let uu____14466 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1948_14465.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1948_14465.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1948_14465.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1948_14465.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1948_14465.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1948_14465.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1948_14465.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1948_14465.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1948_14465.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1948_14465.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1948_14465.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1948_14465.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1948_14465.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1948_14465.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1948_14465.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1948_14465.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1948_14465.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1948_14465.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1948_14465.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1948_14465.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1948_14465.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1948_14465.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1948_14465.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1948_14465.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1948_14465.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1948_14465.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1948_14465.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1948_14465.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1948_14465.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1948_14465.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1948_14465.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1948_14465.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1948_14465.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1948_14465.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14466;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1948_14465.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1948_14465.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1948_14465.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1948_14465.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1948_14465.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1948_14465.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1948_14465.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1948_14465.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1948_14465.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver )
           ->
           ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
              ();
            env)
       | FStar_Syntax_Syntax.Sig_pragma uu____14468 -> env
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14469 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____14479 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____14479) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____14480,uu____14481,uu____14482) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_14487  ->
                   match uu___5_14487 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____14490 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____14492,uu____14493) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_14502  ->
                   match uu___5_14502 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____14505 -> false))
           -> env
       | uu____14507 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____14576 se =
        match uu____14576 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____14629 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____14629
              then
                let uu____14632 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____14632
              else ());
             (let uu____14637 = tc_decl env1 se  in
              match uu____14637 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____14690 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____14690
                             then
                               let uu____14694 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____14694
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____14710 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____14710
                             then
                               let uu____14714 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____14714
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
                    (let uu____14731 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____14731
                     then
                       let uu____14736 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____14745 =
                                  let uu____14747 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____14747 "\n"  in
                                Prims.op_Hat s uu____14745) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____14736
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____14757 =
                       let uu____14766 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____14766
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____14808 se1 =
                            match uu____14808 with
                            | (exports1,hidden1) ->
                                let uu____14836 = for_export env3 hidden1 se1
                                   in
                                (match uu____14836 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____14757 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____14990 = acc  in
        match uu____14990 with
        | (uu____15025,uu____15026,env1,uu____15028) ->
            let r =
              let uu____15062 =
                let uu____15066 =
                  let uu____15068 = FStar_TypeChecker_Env.current_module env1
                     in
                  FStar_Ident.string_of_lid uu____15068  in
                FStar_Pervasives_Native.Some uu____15066  in
              FStar_Profiling.profile
                (fun uu____15091  -> process_one_decl acc se) uu____15062
                "FStar.TypeChecker.Tc.process_one_decl"
               in
            ((let uu____15094 = FStar_Options.profile_group_by_decls ()  in
              if uu____15094
              then
                let tag =
                  match FStar_Syntax_Util.lids_of_sigelt se with
                  | hd1::uu____15101 -> FStar_Ident.string_of_lid hd1
                  | uu____15104 ->
                      FStar_Range.string_of_range
                        (FStar_Syntax_Util.range_of_sigelt se)
                   in
                FStar_Profiling.report_and_clear tag
              else ());
             r)
         in
      let uu____15109 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____15109 with
      | (ses1,exports,env1,uu____15157) ->
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
          let uu___2048_15195 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2048_15195.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2048_15195.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2048_15195.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2048_15195.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2048_15195.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2048_15195.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2048_15195.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2048_15195.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2048_15195.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2048_15195.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___2048_15195.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___2048_15195.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___2048_15195.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2048_15195.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2048_15195.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___2048_15195.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2048_15195.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___2048_15195.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2048_15195.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___2048_15195.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___2048_15195.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___2048_15195.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2048_15195.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2048_15195.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2048_15195.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2048_15195.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2048_15195.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2048_15195.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2048_15195.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2048_15195.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2048_15195.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2048_15195.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2048_15195.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2048_15195.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___2048_15195.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2048_15195.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2048_15195.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2048_15195.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2048_15195.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2048_15195.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2048_15195.FStar_TypeChecker_Env.strict_args_tab)
          }  in
        let check_term lid univs1 t =
          let uu____15215 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____15215 with
          | (univs2,t1) ->
              ((let uu____15223 =
                  let uu____15225 =
                    let uu____15231 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____15231  in
                  FStar_All.pipe_left uu____15225
                    (FStar_Options.Other "Exports")
                   in
                if uu____15223
                then
                  let uu____15235 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____15237 =
                    let uu____15239 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____15239
                      (FStar_String.concat ", ")
                     in
                  let uu____15256 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____15235 uu____15237 uu____15256
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____15262 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____15262 (fun a1  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____15288 =
             let uu____15290 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____15292 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____15290 uu____15292
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____15288);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15303) ->
              let uu____15312 =
                let uu____15314 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15314  in
              if uu____15312
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____15328,uu____15329) ->
              let t =
                let uu____15341 =
                  let uu____15348 =
                    let uu____15349 =
                      let uu____15364 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____15364)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____15349  in
                  FStar_Syntax_Syntax.mk uu____15348  in
                uu____15341 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____15380,uu____15381,uu____15382) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____15392 =
                let uu____15394 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15394  in
              if uu____15392 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____15402,lbs),uu____15404) ->
              let uu____15415 =
                let uu____15417 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15417  in
              if uu____15415
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
              let uu____15440 =
                let uu____15442 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15442  in
              if uu____15440
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____15463 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____15464 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____15471 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15472 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____15473 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____15474 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____15481 -> ()  in
        let uu____15482 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____15482 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____15588) -> true
             | uu____15590 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____15620 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____15659 ->
                   let uu____15660 =
                     let uu____15667 =
                       let uu____15668 =
                         let uu____15683 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____15683)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____15668  in
                     FStar_Syntax_Syntax.mk uu____15667  in
                   uu____15660 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____15700,uu____15701) ->
            let s1 =
              let uu___2174_15711 = s  in
              let uu____15712 =
                let uu____15713 =
                  let uu____15720 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____15720)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____15713  in
              let uu____15721 =
                let uu____15724 =
                  let uu____15727 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____15727  in
                FStar_Syntax_Syntax.Assumption :: uu____15724  in
              {
                FStar_Syntax_Syntax.sigel = uu____15712;
                FStar_Syntax_Syntax.sigrng =
                  (uu___2174_15711.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____15721;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2174_15711.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___2174_15711.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____15730 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____15755 lbdef =
        match uu____15755 with
        | (uvs,t) ->
            let attrs =
              let uu____15766 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____15766
              then
                let uu____15771 =
                  let uu____15772 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____15772
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____15771 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___2187_15775 = s  in
            let uu____15776 =
              let uu____15779 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____15779  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___2187_15775.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____15776;
              FStar_Syntax_Syntax.sigmeta =
                (uu___2187_15775.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____15797 -> failwith "Impossible!"  in
        let c_opt =
          let uu____15804 = FStar_Syntax_Util.is_unit t  in
          if uu____15804
          then
            let uu____15811 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____15811
          else
            (let uu____15818 =
               let uu____15819 = FStar_Syntax_Subst.compress t  in
               uu____15819.FStar_Syntax_Syntax.n  in
             match uu____15818 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____15826,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____15850 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____15862 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____15862
            then false
            else
              (let uu____15869 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____15869
               then true
               else
                 (let uu____15876 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____15876))
         in
      let extract_sigelt s =
        (let uu____15888 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____15888
         then
           let uu____15891 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____15891
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____15898 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____15918 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____15937 ->
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
                             (lid,uu____15983,uu____15984,uu____15985,uu____15986,uu____15987)
                             ->
                             ((let uu____15997 =
                                 let uu____16000 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____16000  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____15997);
                              (let uu____16049 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____16049 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____16053,uu____16054,uu____16055,uu____16056,uu____16057)
                             ->
                             ((let uu____16065 =
                                 let uu____16068 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____16068  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____16065);
                              sigelts1)
                         | uu____16117 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____16126 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____16126
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____16136 =
                    let uu___2251_16137 = s  in
                    let uu____16138 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2251_16137.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2251_16137.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____16138;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2251_16137.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2251_16137.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____16136])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____16149 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____16149
             then []
             else
               (let uu____16156 = lbs  in
                match uu____16156 with
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
                        (fun uu____16218  ->
                           match uu____16218 with
                           | (uu____16226,t,uu____16228) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____16245  ->
                             match uu____16245 with
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
                           (fun uu____16272  ->
                              match uu____16272 with
                              | (uu____16280,t,uu____16282) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____16294,uu____16295) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____16303 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____16332 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____16332) uu____16303
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____16336 =
                    let uu___2293_16337 = s  in
                    let uu____16338 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2293_16337.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2293_16337.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____16338;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2293_16337.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2293_16337.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____16336]
                else [])
             else
               (let uu____16345 =
                  let uu___2295_16346 = s  in
                  let uu____16347 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___2295_16346.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___2295_16346.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____16347;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___2295_16346.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___2295_16346.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____16345])
         | FStar_Syntax_Syntax.Sig_new_effect uu____16350 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____16351 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____16352 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____16353 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____16366 -> [s])
         in
      let uu___2307_16367 = m  in
      let uu____16368 =
        let uu____16369 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____16369 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___2307_16367.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____16368;
        FStar_Syntax_Syntax.exports =
          (uu___2307_16367.FStar_Syntax_Syntax.exports);
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
        (fun uu____16420  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____16467  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____16482 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____16482
  
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
      (let uu____16571 = FStar_Options.debug_any ()  in
       if uu____16571
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
         let uu___2332_16587 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___2332_16587.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___2332_16587.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___2332_16587.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___2332_16587.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___2332_16587.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___2332_16587.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___2332_16587.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___2332_16587.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___2332_16587.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___2332_16587.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___2332_16587.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___2332_16587.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___2332_16587.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___2332_16587.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___2332_16587.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___2332_16587.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___2332_16587.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___2332_16587.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___2332_16587.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___2332_16587.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___2332_16587.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___2332_16587.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___2332_16587.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___2332_16587.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___2332_16587.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___2332_16587.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___2332_16587.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___2332_16587.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___2332_16587.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___2332_16587.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___2332_16587.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___2332_16587.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___2332_16587.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___2332_16587.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___2332_16587.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___2332_16587.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___2332_16587.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___2332_16587.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___2332_16587.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___2332_16587.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___2332_16587.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___2332_16587.FStar_TypeChecker_Env.strict_args_tab)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____16589 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____16589 with
       | (ses,exports,env3) ->
           ((let uu___2340_16622 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___2340_16622.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___2340_16622.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___2340_16622.FStar_Syntax_Syntax.is_interface)
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
        let uu____16651 = tc_decls env decls  in
        match uu____16651 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___2349_16682 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___2349_16682.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___2349_16682.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___2349_16682.FStar_Syntax_Syntax.is_interface)
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
        let uu____16743 = tc_partial_modul env01 m  in
        match uu____16743 with
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
                (let uu____16780 = FStar_Errors.get_err_count ()  in
                 uu____16780 = Prims.int_zero)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____16791 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____16791
                then
                  let uu____16795 =
                    let uu____16797 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16797 then "" else " (in lax mode) "  in
                  let uu____16805 =
                    let uu____16807 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16807
                    then
                      let uu____16811 =
                        let uu____16813 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.op_Hat uu____16813 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____16811
                    else ""  in
                  let uu____16820 =
                    let uu____16822 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16822
                    then
                      let uu____16826 =
                        let uu____16828 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____16828 "\n"  in
                      Prims.op_Hat "\nto: " uu____16826
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____16795
                    uu____16805 uu____16820
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___2375_16842 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2375_16842.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2375_16842.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2375_16842.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2375_16842.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2375_16842.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2375_16842.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2375_16842.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2375_16842.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2375_16842.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2375_16842.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2375_16842.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2375_16842.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2375_16842.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2375_16842.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2375_16842.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2375_16842.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2375_16842.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2375_16842.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2375_16842.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2375_16842.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2375_16842.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2375_16842.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2375_16842.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2375_16842.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2375_16842.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2375_16842.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2375_16842.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2375_16842.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2375_16842.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2375_16842.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2375_16842.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___2375_16842.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2375_16842.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2375_16842.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2375_16842.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2375_16842.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2375_16842.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2375_16842.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2375_16842.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2375_16842.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2375_16842.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2375_16842.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2375_16842.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let en02 =
                    let uu___2378_16844 = en01  in
                    let uu____16845 =
                      let uu____16860 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____16860, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2378_16844.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2378_16844.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2378_16844.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2378_16844.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2378_16844.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2378_16844.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2378_16844.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2378_16844.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2378_16844.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2378_16844.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2378_16844.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2378_16844.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2378_16844.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2378_16844.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2378_16844.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2378_16844.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2378_16844.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2378_16844.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2378_16844.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2378_16844.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2378_16844.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2378_16844.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2378_16844.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2378_16844.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2378_16844.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2378_16844.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2378_16844.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2378_16844.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2378_16844.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2378_16844.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2378_16844.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____16845;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2378_16844.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2378_16844.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2378_16844.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2378_16844.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2378_16844.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2378_16844.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2378_16844.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2378_16844.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2378_16844.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___2378_16844.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2378_16844.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2378_16844.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let uu____16906 =
                    let uu____16908 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____16908  in
                  if uu____16906
                  then
                    ((let uu____16912 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____16912 (fun a2  -> ()));
                     en02)
                  else en02  in
                let uu____16916 = tc_modul en0 modul_iface true  in
                match uu____16916 with
                | (modul_iface1,env) ->
                    ((let uu___2387_16929 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___2387_16929.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___2387_16929.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___2387_16929.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___2389_16933 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___2389_16933.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___2389_16933.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___2389_16933.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____16936 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____16936 FStar_Util.smap_clear);
               (let uu____16972 =
                  ((let uu____16976 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____16976) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____16979 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____16979)
                   in
                if uu____16972 then check_exports env modul exports else ());
               (let uu____16985 =
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____16985 (fun a3  -> ()));
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
        let uu____17000 =
          let uu____17002 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____17002  in
        push_context env uu____17000  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____17023 =
                         FStar_TypeChecker_Env.lookup_sigelt env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____17026 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____17026 with | (uu____17033,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____17058 = FStar_Options.debug_any ()  in
         if uu____17058
         then
           let uu____17061 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____17061
         else ());
        (let uu____17073 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____17073
         then
           let uu____17076 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____17076
         else ());
        (let env1 =
           let uu___2419_17082 = env  in
           let uu____17083 =
             let uu____17085 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____17085  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___2419_17082.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___2419_17082.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___2419_17082.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___2419_17082.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___2419_17082.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___2419_17082.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___2419_17082.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___2419_17082.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___2419_17082.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___2419_17082.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___2419_17082.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___2419_17082.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___2419_17082.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___2419_17082.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___2419_17082.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___2419_17082.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___2419_17082.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___2419_17082.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___2419_17082.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___2419_17082.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____17083;
             FStar_TypeChecker_Env.lax_universes =
               (uu___2419_17082.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___2419_17082.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___2419_17082.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___2419_17082.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___2419_17082.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___2419_17082.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___2419_17082.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___2419_17082.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___2419_17082.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___2419_17082.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___2419_17082.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___2419_17082.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___2419_17082.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___2419_17082.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___2419_17082.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___2419_17082.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___2419_17082.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___2419_17082.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___2419_17082.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___2419_17082.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___2419_17082.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___2419_17082.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___2419_17082.FStar_TypeChecker_Env.strict_args_tab)
           }  in
         let uu____17087 = tc_modul env1 m b  in
         match uu____17087 with
         | (m1,env2) ->
             ((let uu____17099 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____17099
               then
                 let uu____17102 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____17102
               else ());
              (let uu____17108 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____17108
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
                         let uu____17146 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____17146 with
                         | (univnames1,e) ->
                             let uu___2441_17153 = lb  in
                             let uu____17154 =
                               let uu____17157 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____17157 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2441_17153.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2441_17153.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___2441_17153.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2441_17153.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____17154;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2441_17153.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2441_17153.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___2443_17158 = se  in
                       let uu____17159 =
                         let uu____17160 =
                           let uu____17167 =
                             let uu____17168 = FStar_List.map update lbs  in
                             (b1, uu____17168)  in
                           (uu____17167, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____17160  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____17159;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___2443_17158.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___2443_17158.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___2443_17158.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___2443_17158.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____17176 -> se  in
                 let normalized_module =
                   let uu___2447_17178 = m1  in
                   let uu____17179 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___2447_17178.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____17179;
                     FStar_Syntax_Syntax.exports =
                       (uu___2447_17178.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___2447_17178.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____17180 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____17180
               else ());
              (m1, env2)))
  