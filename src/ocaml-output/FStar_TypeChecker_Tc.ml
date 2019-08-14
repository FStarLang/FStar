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
                                      FStar_TypeChecker_Normalize.remove_uvar_solutions
                                        env k
                                       in
                                    let uu____2685 =
                                      FStar_Syntax_Subst.close_univ_vars
                                        stronger_us k1
                                       in
                                    (stronger_us, stronger_t, uu____2685))))))))
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
              (let uu____2721 =
                 let uu____2726 =
                   FStar_Syntax_Subst.univ_var_opening
                     act.FStar_Syntax_Syntax.action_univs
                    in
                 match uu____2726 with
                 | (usubst,us) ->
                     let uu____2749 =
                       FStar_TypeChecker_Env.push_univ_vars env us  in
                     let uu____2750 =
                       let uu___346_2751 = act  in
                       let uu____2752 =
                         FStar_Syntax_Subst.subst usubst
                           act.FStar_Syntax_Syntax.action_defn
                          in
                       let uu____2753 =
                         FStar_Syntax_Subst.subst usubst
                           act.FStar_Syntax_Syntax.action_typ
                          in
                       {
                         FStar_Syntax_Syntax.action_name =
                           (uu___346_2751.FStar_Syntax_Syntax.action_name);
                         FStar_Syntax_Syntax.action_unqualified_name =
                           (uu___346_2751.FStar_Syntax_Syntax.action_unqualified_name);
                         FStar_Syntax_Syntax.action_univs = us;
                         FStar_Syntax_Syntax.action_params =
                           (uu___346_2751.FStar_Syntax_Syntax.action_params);
                         FStar_Syntax_Syntax.action_defn = uu____2752;
                         FStar_Syntax_Syntax.action_typ = uu____2753
                       }  in
                     (uu____2749, uu____2750)
                  in
               match uu____2721 with
               | (env1,act1) ->
                   let act_typ =
                     let uu____2757 =
                       let uu____2758 =
                         FStar_Syntax_Subst.compress
                           act1.FStar_Syntax_Syntax.action_typ
                          in
                       uu____2758.FStar_Syntax_Syntax.n  in
                     match uu____2757 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                         let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
                         let uu____2784 =
                           FStar_Ident.lid_equals
                             ct.FStar_Syntax_Syntax.effect_name
                             ed.FStar_Syntax_Syntax.mname
                            in
                         if uu____2784
                         then
                           let repr_ts =
                             let uu____2788 = repr  in
                             match uu____2788 with
                             | (us,t,uu____2803) -> (us, t)  in
                           let repr1 =
                             let uu____2821 =
                               FStar_TypeChecker_Env.inst_tscheme_with
                                 repr_ts ct.FStar_Syntax_Syntax.comp_univs
                                in
                             FStar_All.pipe_right uu____2821
                               FStar_Pervasives_Native.snd
                              in
                           let c1 =
                             let uu____2833 =
                               let uu____2834 =
                                 let uu____2839 =
                                   let uu____2840 =
                                     FStar_Syntax_Syntax.as_arg
                                       ct.FStar_Syntax_Syntax.result_typ
                                      in
                                   uu____2840 ::
                                     (ct.FStar_Syntax_Syntax.effect_args)
                                    in
                                 FStar_Syntax_Syntax.mk_Tm_app repr1
                                   uu____2839
                                  in
                               uu____2834 FStar_Pervasives_Native.None r  in
                             FStar_All.pipe_right uu____2833
                               FStar_Syntax_Syntax.mk_Total
                              in
                           FStar_Syntax_Util.arrow bs c1
                         else act1.FStar_Syntax_Syntax.action_typ
                     | uu____2861 -> act1.FStar_Syntax_Syntax.action_typ  in
                   let uu____2862 =
                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                       act_typ
                      in
                   (match uu____2862 with
                    | (act_typ1,uu____2870,g_t) ->
                        let uu____2872 =
                          let uu____2879 =
                            let uu___370_2880 =
                              FStar_TypeChecker_Env.set_expected_typ env1
                                act_typ1
                               in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___370_2880.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___370_2880.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___370_2880.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___370_2880.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___370_2880.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___370_2880.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___370_2880.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___370_2880.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___370_2880.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___370_2880.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___370_2880.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp = false;
                              FStar_TypeChecker_Env.effects =
                                (uu___370_2880.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___370_2880.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___370_2880.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___370_2880.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___370_2880.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___370_2880.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___370_2880.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___370_2880.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax =
                                (uu___370_2880.FStar_TypeChecker_Env.lax);
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___370_2880.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___370_2880.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___370_2880.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___370_2880.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___370_2880.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___370_2880.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___370_2880.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___370_2880.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___370_2880.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___370_2880.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___370_2880.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___370_2880.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___370_2880.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___370_2880.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___370_2880.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___370_2880.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___370_2880.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___370_2880.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___370_2880.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___370_2880.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___370_2880.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___370_2880.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___370_2880.FStar_TypeChecker_Env.strict_args_tab)
                            }  in
                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                            uu____2879 act1.FStar_Syntax_Syntax.action_defn
                           in
                        (match uu____2872 with
                         | (act_defn,uu____2883,g_d) ->
                             ((let uu____2886 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env1)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____2886
                               then
                                 let uu____2891 =
                                   FStar_Syntax_Print.term_to_string act_defn
                                    in
                                 let uu____2893 =
                                   FStar_Syntax_Print.term_to_string act_typ1
                                    in
                                 FStar_Util.print2
                                   "Typechecked action definition: %s and action type: %s\n"
                                   uu____2891 uu____2893
                               else ());
                              (let uu____2898 =
                                 let act_typ2 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Beta] env1
                                     act_typ1
                                    in
                                 let uu____2906 =
                                   let uu____2907 =
                                     FStar_Syntax_Subst.compress act_typ2  in
                                   uu____2907.FStar_Syntax_Syntax.n  in
                                 match uu____2906 with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                     let bs1 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     let env2 =
                                       FStar_TypeChecker_Env.push_binders
                                         env1 bs1
                                        in
                                     let uu____2940 =
                                       FStar_Syntax_Util.type_u ()  in
                                     (match uu____2940 with
                                      | (t,u) ->
                                          let uu____2953 =
                                            FStar_TypeChecker_Util.new_implicit_var
                                              "" r env2 t
                                             in
                                          (match uu____2953 with
                                           | (a_tm,uu____2974,g_tm) ->
                                               let uu____2988 =
                                                 fresh_repr r env2 u a_tm  in
                                               (match uu____2988 with
                                                | (repr1,g) ->
                                                    let uu____3001 =
                                                      let uu____3004 =
                                                        let uu____3007 =
                                                          let uu____3010 =
                                                            FStar_TypeChecker_Env.new_u_univ
                                                              ()
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____3010
                                                            (fun _3013  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _3013)
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total'
                                                          repr1 uu____3007
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____3004
                                                       in
                                                    let uu____3014 =
                                                      FStar_TypeChecker_Env.conj_guard
                                                        g g_tm
                                                       in
                                                    (uu____3001, uu____3014))))
                                 | uu____3017 ->
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                         "") r
                                  in
                               match uu____2898 with
                               | (k,g_k) ->
                                   ((let uu____3033 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other
                                            "LayeredEffects")
                                        in
                                     if uu____3033
                                     then
                                       let uu____3038 =
                                         FStar_Syntax_Print.term_to_string k
                                          in
                                       FStar_Util.print1
                                         "Expected action type: %s\n"
                                         uu____3038
                                     else ());
                                    (let g =
                                       FStar_TypeChecker_Rel.teq env1
                                         act_typ1 k
                                        in
                                     FStar_List.iter
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1) [g_t; g_d; g_k; g];
                                     (let uu____3046 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____3046
                                      then
                                        let uu____3051 =
                                          FStar_Syntax_Print.term_to_string k
                                           in
                                        FStar_Util.print1
                                          "Expected action type after unification: %s\n"
                                          uu____3051
                                      else ());
                                     (let act_typ2 =
                                        let repr_args t =
                                          let uu____3075 =
                                            let uu____3076 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____3076.FStar_Syntax_Syntax.n
                                             in
                                          match uu____3075 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (head1,a::is) ->
                                              let uu____3128 =
                                                let uu____3129 =
                                                  FStar_Syntax_Subst.compress
                                                    head1
                                                   in
                                                uu____3129.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____3128 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (uu____3138,us) ->
                                                   (us,
                                                     (FStar_Pervasives_Native.fst
                                                        a), is)
                                               | uu____3148 ->
                                                   failwith "Impossible!")
                                          | uu____3156 ->
                                              failwith "Impossible!"
                                           in
                                        let k1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Env.Beta] env1
                                            k
                                           in
                                        let uu____3165 =
                                          let uu____3166 =
                                            FStar_Syntax_Subst.compress k1
                                             in
                                          uu____3166.FStar_Syntax_Syntax.n
                                           in
                                        match uu____3165 with
                                        | FStar_Syntax_Syntax.Tm_arrow 
                                            (bs,c) ->
                                            let uu____3191 =
                                              FStar_Syntax_Subst.open_comp bs
                                                c
                                               in
                                            (match uu____3191 with
                                             | (bs1,c1) ->
                                                 let uu____3198 =
                                                   repr_args
                                                     (FStar_Syntax_Util.comp_result
                                                        c1)
                                                    in
                                                 (match uu____3198 with
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
                                                      let uu____3209 =
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          ct
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____3209))
                                        | uu____3212 ->
                                            failwith "Impossible!"
                                         in
                                      (let uu____3215 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____3215
                                       then
                                         let uu____3220 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ2
                                            in
                                         FStar_Util.print1
                                           "Action type after injecting it into the monad: %s\n"
                                           uu____3220
                                       else ());
                                      (let act2 =
                                         if
                                           act1.FStar_Syntax_Syntax.action_univs
                                             = []
                                         then
                                           let uu____3229 =
                                             FStar_TypeChecker_Util.generalize_universes
                                               env1 act_defn
                                              in
                                           match uu____3229 with
                                           | (us,act_defn1) ->
                                               let uu___440_3240 = act1  in
                                               let uu____3241 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   us act_typ2
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___440_3240.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___440_3240.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = us;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___440_3240.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = act_defn1;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = uu____3241
                                               }
                                         else
                                           (let uu___442_3244 = act1  in
                                            let uu____3245 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                act1.FStar_Syntax_Syntax.action_univs
                                                act_defn
                                               in
                                            let uu____3246 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                act1.FStar_Syntax_Syntax.action_univs
                                                act_typ2
                                               in
                                            {
                                              FStar_Syntax_Syntax.action_name
                                                =
                                                (uu___442_3244.FStar_Syntax_Syntax.action_name);
                                              FStar_Syntax_Syntax.action_unqualified_name
                                                =
                                                (uu___442_3244.FStar_Syntax_Syntax.action_unqualified_name);
                                              FStar_Syntax_Syntax.action_univs
                                                =
                                                (uu___442_3244.FStar_Syntax_Syntax.action_univs);
                                              FStar_Syntax_Syntax.action_params
                                                =
                                                (uu___442_3244.FStar_Syntax_Syntax.action_params);
                                              FStar_Syntax_Syntax.action_defn
                                                = uu____3245;
                                              FStar_Syntax_Syntax.action_typ
                                                = uu____3246
                                            })
                                          in
                                       act2)))))))))
               in
            let fst1 uu____3266 =
              match uu____3266 with | (a,uu____3282,uu____3283) -> a  in
            let snd1 uu____3315 =
              match uu____3315 with | (uu____3330,b,uu____3332) -> b  in
            let thd uu____3364 =
              match uu____3364 with | (uu____3379,uu____3380,c) -> c  in
            let uu___460_3394 = ed  in
            let uu____3395 =
              FStar_All.pipe_right
                ((fst1 stronger_repr), (snd1 stronger_repr))
                (fun _3404  -> FStar_Pervasives_Native.Some _3404)
               in
            let uu____3405 =
              FStar_List.map (tc_action env0) ed.FStar_Syntax_Syntax.actions
               in
            {
              FStar_Syntax_Syntax.is_layered =
                (uu___460_3394.FStar_Syntax_Syntax.is_layered);
              FStar_Syntax_Syntax.cattributes =
                (uu___460_3394.FStar_Syntax_Syntax.cattributes);
              FStar_Syntax_Syntax.mname =
                (uu___460_3394.FStar_Syntax_Syntax.mname);
              FStar_Syntax_Syntax.univs =
                (uu___460_3394.FStar_Syntax_Syntax.univs);
              FStar_Syntax_Syntax.binders =
                (uu___460_3394.FStar_Syntax_Syntax.binders);
              FStar_Syntax_Syntax.signature =
                ((fst1 signature), (snd1 signature));
              FStar_Syntax_Syntax.ret_wp =
                ((fst1 return_repr), (thd return_repr));
              FStar_Syntax_Syntax.bind_wp =
                ((fst1 bind_repr), (thd bind_repr));
              FStar_Syntax_Syntax.stronger =
                ((fst1 stronger_repr), (thd stronger_repr));
              FStar_Syntax_Syntax.match_wps =
                (uu___460_3394.FStar_Syntax_Syntax.match_wps);
              FStar_Syntax_Syntax.trivial =
                (uu___460_3394.FStar_Syntax_Syntax.trivial);
              FStar_Syntax_Syntax.repr = ((fst1 repr), (snd1 repr));
              FStar_Syntax_Syntax.return_repr =
                ((fst1 return_repr), (snd1 return_repr));
              FStar_Syntax_Syntax.bind_repr =
                ((fst1 bind_repr), (snd1 bind_repr));
              FStar_Syntax_Syntax.stronger_repr = uu____3395;
              FStar_Syntax_Syntax.actions = uu____3405;
              FStar_Syntax_Syntax.eff_attrs =
                (uu___460_3394.FStar_Syntax_Syntax.eff_attrs)
            }))))))
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____3448 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____3448
       then
         let uu____3453 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____3453
       else ());
      (let uu____3458 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____3458 with
       | (us,lift) ->
           let r = lift.FStar_Syntax_Syntax.pos  in
           (if (FStar_List.length us) <> Prims.int_zero
            then
              (let uu____3492 =
                 let uu____3494 = FStar_Syntax_Print.sub_eff_to_string sub1
                    in
                 Prims.op_Hat
                   "Unexpected number of universes in typechecking %s"
                   uu____3494
                  in
               failwith uu____3492)
            else ();
            (let uu____3499 =
               FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env0 lift  in
             match uu____3499 with
             | (lift1,lc,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env0 g;
                  (let lift_ty =
                     FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                       (FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Beta] env0)
                      in
                   (let uu____3516 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                        (FStar_Options.Other "LayeredEffects")
                       in
                    if uu____3516
                    then
                      let uu____3521 =
                        FStar_Syntax_Print.term_to_string lift1  in
                      let uu____3523 =
                        FStar_Syntax_Print.term_to_string lift_ty  in
                      FStar_Util.print2
                        "Typechecked lift: %s and lift_ty: %s\n" uu____3521
                        uu____3523
                    else ());
                   (let uu____3528 =
                      let uu____3535 =
                        let uu____3540 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____3540
                          (fun uu____3557  ->
                             match uu____3557 with
                             | (t,u) ->
                                 let uu____3568 =
                                   let uu____3569 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t
                                      in
                                   FStar_All.pipe_right uu____3569
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____3568, u))
                         in
                      match uu____3535 with
                      | (a,u_a) ->
                          let uu____3579 =
                            let uu____3586 =
                              FStar_TypeChecker_Env.lookup_effect_lid env0
                                sub1.FStar_Syntax_Syntax.source
                               in
                            monad_signature env0
                              sub1.FStar_Syntax_Syntax.source uu____3586
                             in
                          (match uu____3579 with
                           | (a',wp_sort_a') ->
                               let src_wp_sort_a =
                                 let uu____3600 =
                                   let uu____3603 =
                                     let uu____3604 =
                                       let uu____3611 =
                                         let uu____3614 =
                                           FStar_All.pipe_right a
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_All.pipe_right uu____3614
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       (a', uu____3611)  in
                                     FStar_Syntax_Syntax.NT uu____3604  in
                                   [uu____3603]  in
                                 FStar_Syntax_Subst.subst uu____3600
                                   wp_sort_a'
                                  in
                               let wp =
                                 let uu____3634 =
                                   FStar_Syntax_Syntax.gen_bv "wp"
                                     FStar_Pervasives_Native.None
                                     src_wp_sort_a
                                    in
                                 FStar_All.pipe_right uu____3634
                                   FStar_Syntax_Syntax.mk_binder
                                  in
                               let rest_bs =
                                 let uu____3651 =
                                   let uu____3652 =
                                     FStar_Syntax_Subst.compress lift_ty  in
                                   uu____3652.FStar_Syntax_Syntax.n  in
                                 match uu____3651 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____3664) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (3))
                                     ->
                                     let uu____3692 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____3692 with
                                      | (a'1,uu____3702)::(wp',uu____3704)::bs1
                                          ->
                                          let uu____3734 =
                                            FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 Prims.int_one) bs1
                                             in
                                          (match uu____3734 with
                                           | (bs2,uu____3777) ->
                                               let substs =
                                                 let uu____3813 =
                                                   let uu____3814 =
                                                     let uu____3821 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a)
                                                        in
                                                     (a'1, uu____3821)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____3814
                                                    in
                                                 let uu____3828 =
                                                   let uu____3831 =
                                                     let uu____3832 =
                                                       let uu____3839 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              wp)
                                                          in
                                                       (wp', uu____3839)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____3832
                                                      in
                                                   [uu____3831]  in
                                                 uu____3813 :: uu____3828  in
                                               FStar_Syntax_Subst.subst_binders
                                                 substs bs2)
                                      | uu____3846 -> failwith "Impossible!")
                                 | uu____3856 ->
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_UnexpectedEffect,
                                         "") r
                                  in
                               let f =
                                 let f_sort =
                                   let uu____3877 =
                                     let uu____3886 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_Syntax_Syntax.t_unit
                                        in
                                     [uu____3886]  in
                                   let uu____3905 =
                                     let uu____3908 =
                                       let uu____3909 =
                                         let uu____3912 =
                                           FStar_All.pipe_right a
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_All.pipe_right uu____3912
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       let uu____3923 =
                                         let uu____3934 =
                                           let uu____3943 =
                                             let uu____3944 =
                                               FStar_All.pipe_right wp
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____3944
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           FStar_All.pipe_right uu____3943
                                             FStar_Syntax_Syntax.as_arg
                                            in
                                         [uu____3934]  in
                                       {
                                         FStar_Syntax_Syntax.comp_univs =
                                           [u_a];
                                         FStar_Syntax_Syntax.effect_name =
                                           (sub1.FStar_Syntax_Syntax.source);
                                         FStar_Syntax_Syntax.result_typ =
                                           uu____3909;
                                         FStar_Syntax_Syntax.effect_args =
                                           uu____3923;
                                         FStar_Syntax_Syntax.flags = []
                                       }  in
                                     FStar_Syntax_Syntax.mk_Comp uu____3908
                                      in
                                   FStar_Syntax_Util.arrow uu____3877
                                     uu____3905
                                    in
                                 let uu____3977 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None f_sort
                                    in
                                 FStar_All.pipe_right uu____3977
                                   FStar_Syntax_Syntax.mk_binder
                                  in
                               let bs = a :: wp ::
                                 (FStar_List.append rest_bs [f])  in
                               let uu____4024 =
                                 let uu____4029 =
                                   FStar_TypeChecker_Env.push_binders env0 bs
                                    in
                                 let uu____4030 =
                                   let uu____4031 =
                                     FStar_All.pipe_right a
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____4031
                                     FStar_Syntax_Syntax.bv_to_name
                                    in
                                 FStar_TypeChecker_Util.fresh_layered_effect_repr_en
                                   uu____4029 r
                                   sub1.FStar_Syntax_Syntax.target u_a
                                   uu____4030
                                  in
                               (match uu____4024 with
                                | (repr,g_repr) ->
                                    let uu____4048 =
                                      let uu____4051 =
                                        let uu____4054 =
                                          let uu____4057 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_All.pipe_right uu____4057
                                            (fun _4060  ->
                                               FStar_Pervasives_Native.Some
                                                 _4060)
                                           in
                                        FStar_Syntax_Syntax.mk_Total' repr
                                          uu____4054
                                         in
                                      FStar_Syntax_Util.arrow bs uu____4051
                                       in
                                    (uu____4048, g_repr)))
                       in
                    match uu____3528 with
                    | (k,g_k) ->
                        ((let uu____4070 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____4070
                          then
                            let uu____4075 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print1 "Before unification k: %s\n"
                              uu____4075
                          else ());
                         (let g1 = FStar_TypeChecker_Rel.teq env0 lift_ty k
                             in
                          FStar_TypeChecker_Rel.force_trivial_guard env0 g_k;
                          FStar_TypeChecker_Rel.force_trivial_guard env0 g1;
                          (let uu____4084 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffects")
                              in
                           if uu____4084
                           then
                             let uu____4089 =
                               FStar_Syntax_Print.term_to_string k  in
                             FStar_Util.print1 "After unification k: %s\n"
                               uu____4089
                           else ());
                          (let uu____4094 =
                             FStar_TypeChecker_Util.generalize_universes env0
                               lift1
                              in
                           match uu____4094 with
                           | (us1,lift2) ->
                               let lift_wp =
                                 let uu____4108 =
                                   let uu____4109 =
                                     let uu____4114 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env0 us1
                                        in
                                     FStar_TypeChecker_Normalize.remove_uvar_solutions
                                       uu____4114
                                      in
                                   FStar_All.pipe_right k uu____4109  in
                                 FStar_All.pipe_right uu____4108
                                   (FStar_Syntax_Subst.close_univ_vars us1)
                                  in
                               let sub2 =
                                 let uu___531_4118 = sub1  in
                                 {
                                   FStar_Syntax_Syntax.source =
                                     (uu___531_4118.FStar_Syntax_Syntax.source);
                                   FStar_Syntax_Syntax.target =
                                     (uu___531_4118.FStar_Syntax_Syntax.target);
                                   FStar_Syntax_Syntax.lift_wp =
                                     (FStar_Pervasives_Native.Some
                                        (us1, lift_wp));
                                   FStar_Syntax_Syntax.lift =
                                     (FStar_Pervasives_Native.Some
                                        (us1, lift2))
                                 }  in
                               ((let uu____4128 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env0)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____4128
                                 then
                                   let uu____4133 =
                                     FStar_Syntax_Print.sub_eff_to_string
                                       sub2
                                      in
                                   FStar_Util.print1 "Final sub_effect: %s\n"
                                     uu____4133
                                 else ());
                                sub2))))))))))
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      (let uu____4150 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "ED")
          in
       if uu____4150
       then
         let uu____4155 = FStar_Syntax_Print.eff_decl_to_string false ed  in
         FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____4155
       else ());
      (let uu____4161 =
         let uu____4166 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____4166 with
         | (ed_univs_subst,ed_univs) ->
             let bs =
               let uu____4190 =
                 FStar_Syntax_Subst.subst_binders ed_univs_subst
                   ed.FStar_Syntax_Syntax.binders
                  in
               FStar_Syntax_Subst.open_binders uu____4190  in
             let uu____4191 =
               let uu____4198 =
                 FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
               FStar_TypeChecker_TcTerm.tc_tparams uu____4198 bs  in
             (match uu____4191 with
              | (bs1,uu____4204,uu____4205) ->
                  let uu____4206 =
                    let tmp_t =
                      let uu____4216 =
                        let uu____4219 =
                          FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                            (fun _4224  -> FStar_Pervasives_Native.Some _4224)
                           in
                        FStar_Syntax_Syntax.mk_Total'
                          FStar_Syntax_Syntax.t_unit uu____4219
                         in
                      FStar_Syntax_Util.arrow bs1 uu____4216  in
                    let uu____4225 =
                      FStar_TypeChecker_Util.generalize_universes env0 tmp_t
                       in
                    match uu____4225 with
                    | (us,tmp_t1) ->
                        let uu____4242 =
                          let uu____4243 =
                            let uu____4244 =
                              FStar_All.pipe_right tmp_t1
                                FStar_Syntax_Util.arrow_formals
                               in
                            FStar_All.pipe_right uu____4244
                              FStar_Pervasives_Native.fst
                             in
                          FStar_All.pipe_right uu____4243
                            FStar_Syntax_Subst.close_binders
                           in
                        (us, uu____4242)
                     in
                  (match uu____4206 with
                   | (us,bs2) ->
                       (match ed_univs with
                        | [] -> (us, bs2)
                        | uu____4313 ->
                            let uu____4316 =
                              ((FStar_List.length ed_univs) =
                                 (FStar_List.length us))
                                &&
                                (FStar_List.forall2
                                   (fun u1  ->
                                      fun u2  ->
                                        let uu____4323 =
                                          FStar_Syntax_Syntax.order_univ_name
                                            u1 u2
                                           in
                                        uu____4323 = Prims.int_zero) ed_univs
                                   us)
                               in
                            if uu____4316
                            then (us, bs2)
                            else
                              (let uu____4334 =
                                 let uu____4340 =
                                   let uu____4342 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length ed_univs)
                                      in
                                   let uu____4344 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length us)
                                      in
                                   FStar_Util.format3
                                     "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                     uu____4342 uu____4344
                                    in
                                 (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                   uu____4340)
                                  in
                               let uu____4348 =
                                 FStar_Ident.range_of_lid
                                   ed.FStar_Syntax_Syntax.mname
                                  in
                               FStar_Errors.raise_error uu____4334 uu____4348))))
          in
       match uu____4161 with
       | (us,bs) ->
           let ed1 =
             let uu___563_4356 = ed  in
             {
               FStar_Syntax_Syntax.is_layered =
                 (uu___563_4356.FStar_Syntax_Syntax.is_layered);
               FStar_Syntax_Syntax.cattributes =
                 (uu___563_4356.FStar_Syntax_Syntax.cattributes);
               FStar_Syntax_Syntax.mname =
                 (uu___563_4356.FStar_Syntax_Syntax.mname);
               FStar_Syntax_Syntax.univs = us;
               FStar_Syntax_Syntax.binders = bs;
               FStar_Syntax_Syntax.signature =
                 (uu___563_4356.FStar_Syntax_Syntax.signature);
               FStar_Syntax_Syntax.ret_wp =
                 (uu___563_4356.FStar_Syntax_Syntax.ret_wp);
               FStar_Syntax_Syntax.bind_wp =
                 (uu___563_4356.FStar_Syntax_Syntax.bind_wp);
               FStar_Syntax_Syntax.stronger =
                 (uu___563_4356.FStar_Syntax_Syntax.stronger);
               FStar_Syntax_Syntax.match_wps =
                 (uu___563_4356.FStar_Syntax_Syntax.match_wps);
               FStar_Syntax_Syntax.trivial =
                 (uu___563_4356.FStar_Syntax_Syntax.trivial);
               FStar_Syntax_Syntax.repr =
                 (uu___563_4356.FStar_Syntax_Syntax.repr);
               FStar_Syntax_Syntax.return_repr =
                 (uu___563_4356.FStar_Syntax_Syntax.return_repr);
               FStar_Syntax_Syntax.bind_repr =
                 (uu___563_4356.FStar_Syntax_Syntax.bind_repr);
               FStar_Syntax_Syntax.stronger_repr =
                 (uu___563_4356.FStar_Syntax_Syntax.stronger_repr);
               FStar_Syntax_Syntax.actions =
                 (uu___563_4356.FStar_Syntax_Syntax.actions);
               FStar_Syntax_Syntax.eff_attrs =
                 (uu___563_4356.FStar_Syntax_Syntax.eff_attrs)
             }  in
           let uu____4357 = FStar_Syntax_Subst.univ_var_opening us  in
           (match uu____4357 with
            | (ed_univs_subst,ed_univs) ->
                let uu____4376 =
                  let uu____4381 =
                    FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                  FStar_Syntax_Subst.open_binders' uu____4381  in
                (match uu____4376 with
                 | (ed_bs,ed_bs_subst) ->
                     let ed2 =
                       let op uu____4402 =
                         match uu____4402 with
                         | (us1,t) ->
                             let t1 =
                               let uu____4422 =
                                 FStar_Syntax_Subst.shift_subst
                                   ((FStar_List.length ed_bs) +
                                      (FStar_List.length us1)) ed_univs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____4422 t  in
                             let uu____4431 =
                               let uu____4432 =
                                 FStar_Syntax_Subst.shift_subst
                                   (FStar_List.length us1) ed_bs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____4432 t1  in
                             (us1, uu____4431)
                          in
                       let uu___577_4437 = ed1  in
                       let uu____4438 = op ed1.FStar_Syntax_Syntax.signature
                          in
                       let uu____4439 = op ed1.FStar_Syntax_Syntax.ret_wp  in
                       let uu____4440 = op ed1.FStar_Syntax_Syntax.bind_wp
                          in
                       let uu____4441 = op ed1.FStar_Syntax_Syntax.stronger
                          in
                       let uu____4442 =
                         FStar_Syntax_Util.map_match_wps op
                           ed1.FStar_Syntax_Syntax.match_wps
                          in
                       let uu____4447 =
                         FStar_Util.map_opt ed1.FStar_Syntax_Syntax.trivial
                           op
                          in
                       let uu____4450 = op ed1.FStar_Syntax_Syntax.repr  in
                       let uu____4451 =
                         op ed1.FStar_Syntax_Syntax.return_repr  in
                       let uu____4452 = op ed1.FStar_Syntax_Syntax.bind_repr
                          in
                       let uu____4453 =
                         FStar_List.map
                           (fun a  ->
                              let uu___580_4461 = a  in
                              let uu____4462 =
                                let uu____4463 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_defn))
                                   in
                                FStar_Pervasives_Native.snd uu____4463  in
                              let uu____4474 =
                                let uu____4475 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_typ))
                                   in
                                FStar_Pervasives_Native.snd uu____4475  in
                              {
                                FStar_Syntax_Syntax.action_name =
                                  (uu___580_4461.FStar_Syntax_Syntax.action_name);
                                FStar_Syntax_Syntax.action_unqualified_name =
                                  (uu___580_4461.FStar_Syntax_Syntax.action_unqualified_name);
                                FStar_Syntax_Syntax.action_univs =
                                  (uu___580_4461.FStar_Syntax_Syntax.action_univs);
                                FStar_Syntax_Syntax.action_params =
                                  (uu___580_4461.FStar_Syntax_Syntax.action_params);
                                FStar_Syntax_Syntax.action_defn = uu____4462;
                                FStar_Syntax_Syntax.action_typ = uu____4474
                              }) ed1.FStar_Syntax_Syntax.actions
                          in
                       {
                         FStar_Syntax_Syntax.is_layered =
                           (uu___577_4437.FStar_Syntax_Syntax.is_layered);
                         FStar_Syntax_Syntax.cattributes =
                           (uu___577_4437.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.mname =
                           (uu___577_4437.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.univs =
                           (uu___577_4437.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___577_4437.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature = uu____4438;
                         FStar_Syntax_Syntax.ret_wp = uu____4439;
                         FStar_Syntax_Syntax.bind_wp = uu____4440;
                         FStar_Syntax_Syntax.stronger = uu____4441;
                         FStar_Syntax_Syntax.match_wps = uu____4442;
                         FStar_Syntax_Syntax.trivial = uu____4447;
                         FStar_Syntax_Syntax.repr = uu____4450;
                         FStar_Syntax_Syntax.return_repr = uu____4451;
                         FStar_Syntax_Syntax.bind_repr = uu____4452;
                         FStar_Syntax_Syntax.stronger_repr =
                           FStar_Pervasives_Native.None;
                         FStar_Syntax_Syntax.actions = uu____4453;
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___577_4437.FStar_Syntax_Syntax.eff_attrs)
                       }  in
                     ((let uu____4487 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env0)
                           (FStar_Options.Other "ED")
                          in
                       if uu____4487
                       then
                         let uu____4492 =
                           FStar_Syntax_Print.eff_decl_to_string false ed2
                            in
                         FStar_Util.print1
                           "After typechecking binders eff_decl: \n\t%s\n"
                           uu____4492
                       else ());
                      (let env =
                         let uu____4499 =
                           FStar_TypeChecker_Env.push_univ_vars env0 ed_univs
                            in
                         FStar_TypeChecker_Env.push_binders uu____4499 ed_bs
                          in
                       let check_and_gen' comb n1 env_opt uu____4534 k =
                         match uu____4534 with
                         | (us1,t) ->
                             let env1 =
                               if FStar_Util.is_some env_opt
                               then
                                 FStar_All.pipe_right env_opt FStar_Util.must
                               else env  in
                             let uu____4554 =
                               FStar_Syntax_Subst.open_univ_vars us1 t  in
                             (match uu____4554 with
                              | (us2,t1) ->
                                  let t2 =
                                    match k with
                                    | FStar_Pervasives_Native.Some k1 ->
                                        let uu____4563 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env1 us2
                                           in
                                        tc_check_trivial_guard uu____4563 t1
                                          k1
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____4564 =
                                          let uu____4571 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            uu____4571 t1
                                           in
                                        (match uu____4564 with
                                         | (t2,uu____4573,g) ->
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env1 g;
                                              t2))
                                     in
                                  let uu____4576 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env1 t2
                                     in
                                  (match uu____4576 with
                                   | (g_us,t3) ->
                                       (if (FStar_List.length g_us) <> n1
                                        then
                                          (let error =
                                             let uu____4592 =
                                               FStar_Util.string_of_int n1
                                                in
                                             let uu____4594 =
                                               let uu____4596 =
                                                 FStar_All.pipe_right g_us
                                                   FStar_List.length
                                                  in
                                               FStar_All.pipe_right
                                                 uu____4596
                                                 FStar_Util.string_of_int
                                                in
                                             FStar_Util.format4
                                               "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                               (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                               comb uu____4592 uu____4594
                                              in
                                           FStar_Errors.raise_error
                                             (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                               error)
                                             t3.FStar_Syntax_Syntax.pos)
                                        else ();
                                        (match us2 with
                                         | [] -> (g_us, t3)
                                         | uu____4611 ->
                                             let uu____4612 =
                                               ((FStar_List.length us2) =
                                                  (FStar_List.length g_us))
                                                 &&
                                                 (FStar_List.forall2
                                                    (fun u1  ->
                                                       fun u2  ->
                                                         let uu____4619 =
                                                           FStar_Syntax_Syntax.order_univ_name
                                                             u1 u2
                                                            in
                                                         uu____4619 =
                                                           Prims.int_zero)
                                                    us2 g_us)
                                                in
                                             if uu____4612
                                             then (g_us, t3)
                                             else
                                               (let uu____4630 =
                                                  let uu____4636 =
                                                    let uu____4638 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           us2)
                                                       in
                                                    let uu____4640 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           g_us)
                                                       in
                                                    FStar_Util.format4
                                                      "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                      (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      comb uu____4638
                                                      uu____4640
                                                     in
                                                  (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                    uu____4636)
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4630
                                                  t3.FStar_Syntax_Syntax.pos)))))
                          in
                       let signature =
                         check_and_gen' "signature" Prims.int_one
                           FStar_Pervasives_Native.None
                           ed2.FStar_Syntax_Syntax.signature
                           FStar_Pervasives_Native.None
                          in
                       (let uu____4648 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env0)
                            (FStar_Options.Other "ED")
                           in
                        if uu____4648
                        then
                          let uu____4653 =
                            FStar_Syntax_Print.tscheme_to_string signature
                             in
                          FStar_Util.print1 "Typechecked signature: %s\n"
                            uu____4653
                        else ());
                       (let fresh_a_and_wp uu____4669 =
                          let fail1 t =
                            let uu____4682 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env ed2.FStar_Syntax_Syntax.mname t
                               in
                            FStar_Errors.raise_error uu____4682
                              (FStar_Pervasives_Native.snd
                                 ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                             in
                          let uu____4698 =
                            FStar_TypeChecker_Env.inst_tscheme signature  in
                          match uu____4698 with
                          | (uu____4709,signature1) ->
                              let uu____4711 =
                                let uu____4712 =
                                  FStar_Syntax_Subst.compress signature1  in
                                uu____4712.FStar_Syntax_Syntax.n  in
                              (match uu____4711 with
                               | FStar_Syntax_Syntax.Tm_arrow
                                   (bs1,uu____4722) ->
                                   let bs2 =
                                     FStar_Syntax_Subst.open_binders bs1  in
                                   (match bs2 with
                                    | (a,uu____4751)::(wp,uu____4753)::[] ->
                                        (a, (wp.FStar_Syntax_Syntax.sort))
                                    | uu____4782 -> fail1 signature1)
                               | uu____4783 -> fail1 signature1)
                           in
                        let log_combinator s ts =
                          let uu____4797 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "ED")
                             in
                          if uu____4797
                          then
                            let uu____4802 =
                              FStar_Syntax_Print.tscheme_to_string ts  in
                            FStar_Util.print3 "Typechecked %s:%s = %s\n"
                              (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                              s uu____4802
                          else ()  in
                        let ret_wp =
                          let uu____4808 = fresh_a_and_wp ()  in
                          match uu____4808 with
                          | (a,wp_sort) ->
                              let k =
                                let uu____4824 =
                                  let uu____4833 =
                                    FStar_Syntax_Syntax.mk_binder a  in
                                  let uu____4840 =
                                    let uu____4849 =
                                      let uu____4856 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      FStar_Syntax_Syntax.null_binder
                                        uu____4856
                                       in
                                    [uu____4849]  in
                                  uu____4833 :: uu____4840  in
                                let uu____4875 =
                                  FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                FStar_Syntax_Util.arrow uu____4824 uu____4875
                                 in
                              check_and_gen' "ret_wp" Prims.int_one
                                FStar_Pervasives_Native.None
                                ed2.FStar_Syntax_Syntax.ret_wp
                                (FStar_Pervasives_Native.Some k)
                           in
                        log_combinator "ret_wp" ret_wp;
                        (let bind_wp =
                           let uu____4883 = fresh_a_and_wp ()  in
                           match uu____4883 with
                           | (a,wp_sort_a) ->
                               let uu____4896 = fresh_a_and_wp ()  in
                               (match uu____4896 with
                                | (b,wp_sort_b) ->
                                    let wp_sort_a_b =
                                      let uu____4912 =
                                        let uu____4921 =
                                          let uu____4928 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____4928
                                           in
                                        [uu____4921]  in
                                      let uu____4941 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____4912
                                        uu____4941
                                       in
                                    let k =
                                      let uu____4947 =
                                        let uu____4956 =
                                          FStar_Syntax_Syntax.null_binder
                                            FStar_Syntax_Syntax.t_range
                                           in
                                        let uu____4963 =
                                          let uu____4972 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4979 =
                                            let uu____4988 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____4995 =
                                              let uu____5004 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              let uu____5011 =
                                                let uu____5020 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a_b
                                                   in
                                                [uu____5020]  in
                                              uu____5004 :: uu____5011  in
                                            uu____4988 :: uu____4995  in
                                          uu____4972 :: uu____4979  in
                                        uu____4956 :: uu____4963  in
                                      let uu____5063 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____4947
                                        uu____5063
                                       in
                                    check_and_gen' "bind_wp"
                                      (Prims.of_int (2))
                                      FStar_Pervasives_Native.None
                                      ed2.FStar_Syntax_Syntax.bind_wp
                                      (FStar_Pervasives_Native.Some k))
                            in
                         log_combinator "bind_wp" bind_wp;
                         (let stronger =
                            let uu____5071 = fresh_a_and_wp ()  in
                            match uu____5071 with
                            | (a,wp_sort_a) ->
                                let uu____5084 = FStar_Syntax_Util.type_u ()
                                   in
                                (match uu____5084 with
                                 | (t,uu____5090) ->
                                     let k =
                                       let uu____5094 =
                                         let uu____5103 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____5110 =
                                           let uu____5119 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____5126 =
                                             let uu____5135 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____5135]  in
                                           uu____5119 :: uu____5126  in
                                         uu____5103 :: uu____5110  in
                                       let uu____5166 =
                                         FStar_Syntax_Syntax.mk_Total t  in
                                       FStar_Syntax_Util.arrow uu____5094
                                         uu____5166
                                        in
                                     check_and_gen' "stronger" Prims.int_one
                                       FStar_Pervasives_Native.None
                                       ed2.FStar_Syntax_Syntax.stronger
                                       (FStar_Pervasives_Native.Some k))
                             in
                          log_combinator "stronger" stronger;
                          (let match_wps =
                             let uu____5178 =
                               FStar_Syntax_Util.get_match_with_close_wps
                                 ed2.FStar_Syntax_Syntax.match_wps
                                in
                             match uu____5178 with
                             | (if_then_else1,ite_wp,close_wp) ->
                                 let if_then_else2 =
                                   let uu____5193 = fresh_a_and_wp ()  in
                                   match uu____5193 with
                                   | (a,wp_sort_a) ->
                                       let p =
                                         let uu____5207 =
                                           let uu____5210 =
                                             FStar_Ident.range_of_lid
                                               ed2.FStar_Syntax_Syntax.mname
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____5210
                                            in
                                         let uu____5211 =
                                           let uu____5212 =
                                             FStar_Syntax_Util.type_u ()  in
                                           FStar_All.pipe_right uu____5212
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____5207 uu____5211
                                          in
                                       let k =
                                         let uu____5224 =
                                           let uu____5233 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____5240 =
                                             let uu____5249 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 p
                                                in
                                             let uu____5256 =
                                               let uu____5265 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               let uu____5272 =
                                                 let uu____5281 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____5281]  in
                                               uu____5265 :: uu____5272  in
                                             uu____5249 :: uu____5256  in
                                           uu____5233 :: uu____5240  in
                                         let uu____5318 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a
                                            in
                                         FStar_Syntax_Util.arrow uu____5224
                                           uu____5318
                                          in
                                       check_and_gen' "if_then_else"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         if_then_else1
                                         (FStar_Pervasives_Native.Some k)
                                    in
                                 (log_combinator "if_then_else" if_then_else2;
                                  (let ite_wp1 =
                                     let uu____5326 = fresh_a_and_wp ()  in
                                     match uu____5326 with
                                     | (a,wp_sort_a) ->
                                         let k =
                                           let uu____5342 =
                                             let uu____5351 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____5358 =
                                               let uu____5367 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____5367]  in
                                             uu____5351 :: uu____5358  in
                                           let uu____5392 =
                                             FStar_Syntax_Syntax.mk_Total
                                               wp_sort_a
                                              in
                                           FStar_Syntax_Util.arrow uu____5342
                                             uu____5392
                                            in
                                         check_and_gen' "ite_wp"
                                           Prims.int_one
                                           FStar_Pervasives_Native.None
                                           ite_wp
                                           (FStar_Pervasives_Native.Some k)
                                      in
                                   log_combinator "ite_wp" ite_wp1;
                                   (let close_wp1 =
                                      let uu____5400 = fresh_a_and_wp ()  in
                                      match uu____5400 with
                                      | (a,wp_sort_a) ->
                                          let b =
                                            let uu____5414 =
                                              let uu____5417 =
                                                FStar_Ident.range_of_lid
                                                  ed2.FStar_Syntax_Syntax.mname
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____5417
                                               in
                                            let uu____5418 =
                                              let uu____5419 =
                                                FStar_Syntax_Util.type_u ()
                                                 in
                                              FStar_All.pipe_right uu____5419
                                                FStar_Pervasives_Native.fst
                                               in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____5414 uu____5418
                                             in
                                          let wp_sort_b_a =
                                            let uu____5431 =
                                              let uu____5440 =
                                                let uu____5447 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    b
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____5447
                                                 in
                                              [uu____5440]  in
                                            let uu____5460 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____5431 uu____5460
                                             in
                                          let k =
                                            let uu____5466 =
                                              let uu____5475 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____5482 =
                                                let uu____5491 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    b
                                                   in
                                                let uu____5498 =
                                                  let uu____5507 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_b_a
                                                     in
                                                  [uu____5507]  in
                                                uu____5491 :: uu____5498  in
                                              uu____5475 :: uu____5482  in
                                            let uu____5538 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____5466 uu____5538
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
                             let uu____5548 = fresh_a_and_wp ()  in
                             match uu____5548 with
                             | (a,wp_sort_a) ->
                                 let uu____5563 = FStar_Syntax_Util.type_u ()
                                    in
                                 (match uu____5563 with
                                  | (t,uu____5571) ->
                                      let k =
                                        let uu____5575 =
                                          let uu____5584 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____5591 =
                                            let uu____5600 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_sort_a
                                               in
                                            [uu____5600]  in
                                          uu____5584 :: uu____5591  in
                                        let uu____5625 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____5575
                                          uu____5625
                                         in
                                      let trivial =
                                        let uu____5629 =
                                          FStar_All.pipe_right
                                            ed2.FStar_Syntax_Syntax.trivial
                                            FStar_Util.must
                                           in
                                        check_and_gen' "trivial"
                                          Prims.int_one
                                          FStar_Pervasives_Native.None
                                          uu____5629
                                          (FStar_Pervasives_Native.Some k)
                                         in
                                      (log_combinator "trivial" trivial;
                                       FStar_Pervasives_Native.Some trivial))
                              in
                           let uu____5644 =
                             let uu____5655 =
                               let uu____5656 =
                                 FStar_Syntax_Subst.compress
                                   (FStar_Pervasives_Native.snd
                                      ed2.FStar_Syntax_Syntax.repr)
                                  in
                               uu____5656.FStar_Syntax_Syntax.n  in
                             match uu____5655 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____5675 ->
                                 let repr =
                                   let uu____5677 = fresh_a_and_wp ()  in
                                   match uu____5677 with
                                   | (a,wp_sort_a) ->
                                       let uu____5690 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____5690 with
                                        | (t,uu____5696) ->
                                            let k =
                                              let uu____5700 =
                                                let uu____5709 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____5716 =
                                                  let uu____5725 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a
                                                     in
                                                  [uu____5725]  in
                                                uu____5709 :: uu____5716  in
                                              let uu____5750 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____5700 uu____5750
                                               in
                                            check_and_gen' "repr"
                                              Prims.int_one
                                              FStar_Pervasives_Native.None
                                              ed2.FStar_Syntax_Syntax.repr
                                              (FStar_Pervasives_Native.Some k))
                                    in
                                 (log_combinator "repr" repr;
                                  (let mk_repr' t wp =
                                     let uu____5770 =
                                       FStar_TypeChecker_Env.inst_tscheme
                                         repr
                                        in
                                     match uu____5770 with
                                     | (uu____5777,repr1) ->
                                         let repr2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.EraseUniverses;
                                             FStar_TypeChecker_Env.AllowUnboundUniverses]
                                             env repr1
                                            in
                                         let uu____5780 =
                                           let uu____5787 =
                                             let uu____5788 =
                                               let uu____5805 =
                                                 let uu____5816 =
                                                   FStar_All.pipe_right t
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____5833 =
                                                   let uu____5844 =
                                                     FStar_All.pipe_right wp
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____5844]  in
                                                 uu____5816 :: uu____5833  in
                                               (repr2, uu____5805)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5788
                                              in
                                           FStar_Syntax_Syntax.mk uu____5787
                                            in
                                         uu____5780
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                      in
                                   let mk_repr a wp =
                                     let uu____5910 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     mk_repr' uu____5910 wp  in
                                   let destruct_repr t =
                                     let uu____5925 =
                                       let uu____5926 =
                                         FStar_Syntax_Subst.compress t  in
                                       uu____5926.FStar_Syntax_Syntax.n  in
                                     match uu____5925 with
                                     | FStar_Syntax_Syntax.Tm_app
                                         (uu____5937,(t1,uu____5939)::
                                          (wp,uu____5941)::[])
                                         -> (t1, wp)
                                     | uu____6000 ->
                                         failwith "Unexpected repr type"
                                      in
                                   let return_repr =
                                     let uu____6011 = fresh_a_and_wp ()  in
                                     match uu____6011 with
                                     | (a,uu____6019) ->
                                         let x_a =
                                           let uu____6025 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x_a"
                                             FStar_Pervasives_Native.None
                                             uu____6025
                                            in
                                         let res =
                                           let wp =
                                             let uu____6033 =
                                               let uu____6038 =
                                                 let uu____6039 =
                                                   FStar_TypeChecker_Env.inst_tscheme
                                                     ret_wp
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____6039
                                                   FStar_Pervasives_Native.snd
                                                  in
                                               let uu____6048 =
                                                 let uu____6049 =
                                                   let uu____6058 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6058
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____6067 =
                                                   let uu____6078 =
                                                     let uu____6087 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         x_a
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____6087
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____6078]  in
                                                 uu____6049 :: uu____6067  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____6038 uu____6048
                                                in
                                             uu____6033
                                               FStar_Pervasives_Native.None
                                               FStar_Range.dummyRange
                                              in
                                           mk_repr a wp  in
                                         let k =
                                           let uu____6123 =
                                             let uu____6132 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____6139 =
                                               let uu____6148 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   x_a
                                                  in
                                               [uu____6148]  in
                                             uu____6132 :: uu____6139  in
                                           let uu____6173 =
                                             FStar_Syntax_Syntax.mk_Total res
                                              in
                                           FStar_Syntax_Util.arrow uu____6123
                                             uu____6173
                                            in
                                         let uu____6176 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env k
                                            in
                                         (match uu____6176 with
                                          | (k1,uu____6184,uu____6185) ->
                                              let env1 =
                                                let uu____6189 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env
                                                    (FStar_Pervasives_Native.snd
                                                       ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____6189
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
                                        let uu____6200 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            FStar_Parser_Const.range_0
                                            FStar_Syntax_Syntax.delta_constant
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_All.pipe_right uu____6200
                                          FStar_Syntax_Syntax.fv_to_tm
                                         in
                                      let uu____6201 = fresh_a_and_wp ()  in
                                      match uu____6201 with
                                      | (a,wp_sort_a) ->
                                          let uu____6214 = fresh_a_and_wp ()
                                             in
                                          (match uu____6214 with
                                           | (b,wp_sort_b) ->
                                               let wp_sort_a_b =
                                                 let uu____6230 =
                                                   let uu____6239 =
                                                     let uu____6246 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____6246
                                                      in
                                                   [uu____6239]  in
                                                 let uu____6259 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     wp_sort_b
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____6230 uu____6259
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
                                                 let uu____6267 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     a
                                                    in
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "x_a"
                                                   FStar_Pervasives_Native.None
                                                   uu____6267
                                                  in
                                               let wp_g_x =
                                                 let uu____6272 =
                                                   let uu____6277 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       wp_g
                                                      in
                                                   let uu____6278 =
                                                     let uu____6279 =
                                                       let uu____6288 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x_a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____6288
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____6279]  in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     uu____6277 uu____6278
                                                    in
                                                 uu____6272
                                                   FStar_Pervasives_Native.None
                                                   FStar_Range.dummyRange
                                                  in
                                               let res =
                                                 let wp =
                                                   let uu____6319 =
                                                     let uu____6324 =
                                                       let uu____6325 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           bind_wp
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____6325
                                                         FStar_Pervasives_Native.snd
                                                        in
                                                     let uu____6334 =
                                                       let uu____6335 =
                                                         let uu____6338 =
                                                           let uu____6341 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               a
                                                              in
                                                           let uu____6342 =
                                                             let uu____6345 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 b
                                                                in
                                                             let uu____6346 =
                                                               let uu____6349
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_f
                                                                  in
                                                               let uu____6350
                                                                 =
                                                                 let uu____6353
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g
                                                                    in
                                                                 [uu____6353]
                                                                  in
                                                               uu____6349 ::
                                                                 uu____6350
                                                                in
                                                             uu____6345 ::
                                                               uu____6346
                                                              in
                                                           uu____6341 ::
                                                             uu____6342
                                                            in
                                                         r :: uu____6338  in
                                                       FStar_List.map
                                                         FStar_Syntax_Syntax.as_arg
                                                         uu____6335
                                                        in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____6324 uu____6334
                                                      in
                                                   uu____6319
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 mk_repr b wp  in
                                               let maybe_range_arg =
                                                 let uu____6371 =
                                                   FStar_Util.for_some
                                                     (FStar_Syntax_Util.attr_eq
                                                        FStar_Syntax_Util.dm4f_bind_range_attr)
                                                     ed2.FStar_Syntax_Syntax.eff_attrs
                                                    in
                                                 if uu____6371
                                                 then
                                                   let uu____6382 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       FStar_Syntax_Syntax.t_range
                                                      in
                                                   let uu____6389 =
                                                     let uu____6398 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         FStar_Syntax_Syntax.t_range
                                                        in
                                                     [uu____6398]  in
                                                   uu____6382 :: uu____6389
                                                 else []  in
                                               let k =
                                                 let uu____6434 =
                                                   let uu____6443 =
                                                     let uu____6452 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6459 =
                                                       let uu____6468 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           b
                                                          in
                                                       [uu____6468]  in
                                                     uu____6452 :: uu____6459
                                                      in
                                                   let uu____6493 =
                                                     let uu____6502 =
                                                       let uu____6511 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           wp_f
                                                          in
                                                       let uu____6518 =
                                                         let uu____6527 =
                                                           let uu____6534 =
                                                             let uu____6535 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp_f
                                                                in
                                                             mk_repr a
                                                               uu____6535
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____6534
                                                            in
                                                         let uu____6536 =
                                                           let uu____6545 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               wp_g
                                                              in
                                                           let uu____6552 =
                                                             let uu____6561 =
                                                               let uu____6568
                                                                 =
                                                                 let uu____6569
                                                                   =
                                                                   let uu____6578
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                   [uu____6578]
                                                                    in
                                                                 let uu____6597
                                                                   =
                                                                   let uu____6600
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                   FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____6600
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   uu____6569
                                                                   uu____6597
                                                                  in
                                                               FStar_Syntax_Syntax.null_binder
                                                                 uu____6568
                                                                in
                                                             [uu____6561]  in
                                                           uu____6545 ::
                                                             uu____6552
                                                            in
                                                         uu____6527 ::
                                                           uu____6536
                                                          in
                                                       uu____6511 ::
                                                         uu____6518
                                                        in
                                                     FStar_List.append
                                                       maybe_range_arg
                                                       uu____6502
                                                      in
                                                   FStar_List.append
                                                     uu____6443 uu____6493
                                                    in
                                                 let uu____6645 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     res
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____6434 uu____6645
                                                  in
                                               let uu____6648 =
                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                   env k
                                                  in
                                               (match uu____6648 with
                                                | (k1,uu____6656,uu____6657)
                                                    ->
                                                    let env1 =
                                                      FStar_TypeChecker_Env.set_range
                                                        env
                                                        (FStar_Pervasives_Native.snd
                                                           ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                       in
                                                    let env2 =
                                                      FStar_All.pipe_right
                                                        (let uu___778_6669 =
                                                           env1  in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.instantiate_imp);
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             = true;
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.nbe);
                                                           FStar_TypeChecker_Env.strict_args_tab
                                                             =
                                                             (uu___778_6669.FStar_TypeChecker_Env.strict_args_tab)
                                                         })
                                                        (fun _6671  ->
                                                           FStar_Pervasives_Native.Some
                                                             _6671)
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
                                         (let uu____6698 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env, act)
                                            else
                                              (let uu____6712 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____6712 with
                                               | (usubst,uvs) ->
                                                   let uu____6735 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env uvs
                                                      in
                                                   let uu____6736 =
                                                     let uu___791_6737 = act
                                                        in
                                                     let uu____6738 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____6739 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___791_6737.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___791_6737.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___791_6737.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____6738;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____6739
                                                     }  in
                                                   (uu____6735, uu____6736))
                                             in
                                          match uu____6698 with
                                          | (env1,act1) ->
                                              let act_typ =
                                                let uu____6743 =
                                                  let uu____6744 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  uu____6744.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____6743 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs1,c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c
                                                       in
                                                    let uu____6770 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname
                                                       in
                                                    if uu____6770
                                                    then
                                                      let uu____6773 =
                                                        let uu____6776 =
                                                          let uu____6777 =
                                                            let uu____6778 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____6778
                                                             in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____6777
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____6776
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____6773
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____6801 ->
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              let uu____6802 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env1 act_typ
                                                 in
                                              (match uu____6802 with
                                               | (act_typ1,uu____6810,g_t) ->
                                                   let env' =
                                                     let uu___808_6813 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env1 act_typ1
                                                        in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_sig
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.gamma_sig);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.attrtab
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.attrtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.phase1
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.phase1);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.uvar_subtyping
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.uvar_subtyping);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.fv_delta_depths
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.fv_delta_depths);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.postprocess
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.postprocess);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.nbe
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.nbe);
                                                       FStar_TypeChecker_Env.strict_args_tab
                                                         =
                                                         (uu___808_6813.FStar_TypeChecker_Env.strict_args_tab)
                                                     }  in
                                                   ((let uu____6816 =
                                                       FStar_TypeChecker_Env.debug
                                                         env1
                                                         (FStar_Options.Other
                                                            "ED")
                                                        in
                                                     if uu____6816
                                                     then
                                                       let uu____6820 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name
                                                          in
                                                       let uu____6822 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____6824 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1
                                                          in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____6820
                                                         uu____6822
                                                         uu____6824
                                                     else ());
                                                    (let uu____6829 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     match uu____6829 with
                                                     | (act_defn,uu____6837,g_a)
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
                                                         let uu____6841 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2
                                                              in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs1,c) ->
                                                               let uu____6877
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs1 c
                                                                  in
                                                               (match uu____6877
                                                                with
                                                                | (bs2,uu____6889)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____6896
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____6896
                                                                     in
                                                                    let uu____6899
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____6899
                                                                    with
                                                                    | 
                                                                    (k1,uu____6913,g)
                                                                    ->
                                                                    (k1, g)))
                                                           | uu____6917 ->
                                                               let uu____6918
                                                                 =
                                                                 let uu____6924
                                                                   =
                                                                   let uu____6926
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                   let uu____6928
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____6926
                                                                    uu____6928
                                                                    in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____6924)
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____6918
                                                                 act_defn1.FStar_Syntax_Syntax.pos
                                                            in
                                                         (match uu____6841
                                                          with
                                                          | (expected_k,g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env1
                                                                  act_typ2
                                                                  expected_k
                                                                 in
                                                              ((let uu____6946
                                                                  =
                                                                  let uu____6947
                                                                    =
                                                                    let uu____6948
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____6948
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____6947
                                                                   in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env1
                                                                  uu____6946);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____6950
                                                                    =
                                                                    let uu____6951
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____6951.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____6950
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____6976
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____6976
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____6983
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____6983
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____7003
                                                                    =
                                                                    let uu____7004
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____7004]
                                                                     in
                                                                    let uu____7005
                                                                    =
                                                                    let uu____7016
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____7016]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____7003;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____7005;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____7041
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____7041))
                                                                  | uu____7044
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                   in
                                                                let uu____7046
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
                                                                    let uu____7068
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____7068))
                                                                   in
                                                                match uu____7046
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
                                                                    let uu___858_7087
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___858_7087.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___858_7087.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___858_7087.FStar_Syntax_Syntax.action_params);
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
                           match uu____5644 with
                           | (repr,return_repr,bind_repr,actions) ->
                               let cl ts =
                                 let ts1 =
                                   FStar_Syntax_Subst.close_tscheme ed_bs ts
                                    in
                                 let ed_univs_closing =
                                   FStar_Syntax_Subst.univ_var_closing
                                     ed_univs
                                    in
                                 let uu____7112 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length ed_bs)
                                     ed_univs_closing
                                    in
                                 FStar_Syntax_Subst.subst_tscheme uu____7112
                                   ts1
                                  in
                               let ed3 =
                                 let uu___870_7122 = ed2  in
                                 let uu____7123 = cl signature  in
                                 let uu____7124 = cl ret_wp  in
                                 let uu____7125 = cl bind_wp  in
                                 let uu____7126 = cl stronger  in
                                 let uu____7127 =
                                   FStar_Syntax_Util.map_match_wps cl
                                     match_wps
                                    in
                                 let uu____7132 =
                                   FStar_Util.map_opt trivial cl  in
                                 let uu____7135 = cl repr  in
                                 let uu____7136 = cl return_repr  in
                                 let uu____7137 = cl bind_repr  in
                                 let uu____7138 =
                                   FStar_List.map
                                     (fun a  ->
                                        let uu___873_7146 = a  in
                                        let uu____7147 =
                                          let uu____7148 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_All.pipe_right uu____7148
                                            FStar_Pervasives_Native.snd
                                           in
                                        let uu____7173 =
                                          let uu____7174 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_All.pipe_right uu____7174
                                            FStar_Pervasives_Native.snd
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            (uu___873_7146.FStar_Syntax_Syntax.action_name);
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (uu___873_7146.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (uu___873_7146.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (uu___873_7146.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____7147;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____7173
                                        }) actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.is_layered =
                                     (uu___870_7122.FStar_Syntax_Syntax.is_layered);
                                   FStar_Syntax_Syntax.cattributes =
                                     (uu___870_7122.FStar_Syntax_Syntax.cattributes);
                                   FStar_Syntax_Syntax.mname =
                                     (uu___870_7122.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.univs =
                                     (uu___870_7122.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders =
                                     (uu___870_7122.FStar_Syntax_Syntax.binders);
                                   FStar_Syntax_Syntax.signature = uu____7123;
                                   FStar_Syntax_Syntax.ret_wp = uu____7124;
                                   FStar_Syntax_Syntax.bind_wp = uu____7125;
                                   FStar_Syntax_Syntax.stronger = uu____7126;
                                   FStar_Syntax_Syntax.match_wps = uu____7127;
                                   FStar_Syntax_Syntax.trivial = uu____7132;
                                   FStar_Syntax_Syntax.repr = uu____7135;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____7136;
                                   FStar_Syntax_Syntax.bind_repr = uu____7137;
                                   FStar_Syntax_Syntax.stronger_repr =
                                     FStar_Pervasives_Native.None;
                                   FStar_Syntax_Syntax.actions = uu____7138;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (uu___870_7122.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               ((let uu____7200 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____7200
                                 then
                                   let uu____7205 =
                                     FStar_Syntax_Print.eff_decl_to_string
                                       false ed3
                                      in
                                   FStar_Util.print1
                                     "Typechecked effect declaration:\n\t%s\n"
                                     uu____7205
                                 else ());
                                ed3))))))))))
  
let tc_lex_t :
  'Auu____7222 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____7222 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____7257 = FStar_List.hd ses  in
            uu____7257.FStar_Syntax_Syntax.sigrng  in
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
           | uu____7262 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____7268,[],t,uu____7270,uu____7271);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____7273;
               FStar_Syntax_Syntax.sigattrs = uu____7274;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____7276,_t_top,_lex_t_top,_7310,uu____7279);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____7281;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____7282;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____7284,_t_cons,_lex_t_cons,_7318,uu____7287);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____7289;
                 FStar_Syntax_Syntax.sigattrs = uu____7290;_}::[]
               when
               ((_7310 = Prims.int_zero) && (_7318 = Prims.int_zero)) &&
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
                 let uu____7343 =
                   let uu____7350 =
                     let uu____7351 =
                       let uu____7358 =
                         let uu____7361 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____7361
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____7358, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____7351  in
                   FStar_Syntax_Syntax.mk uu____7350  in
                 uu____7343 FStar_Pervasives_Native.None r1  in
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
                   let uu____7376 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7376
                    in
                 let hd1 =
                   let uu____7378 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7378
                    in
                 let tl1 =
                   let uu____7380 =
                     let uu____7381 =
                       let uu____7388 =
                         let uu____7389 =
                           let uu____7396 =
                             let uu____7399 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____7399
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____7396, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____7389  in
                       FStar_Syntax_Syntax.mk uu____7388  in
                     uu____7381 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7380
                    in
                 let res =
                   let uu____7405 =
                     let uu____7412 =
                       let uu____7413 =
                         let uu____7420 =
                           let uu____7423 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____7423
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____7420,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____7413  in
                     FStar_Syntax_Syntax.mk uu____7412  in
                   uu____7405 FStar_Pervasives_Native.None r2  in
                 let uu____7426 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____7426
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
               let uu____7465 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____7465;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____7470 ->
               let err_msg =
                 let uu____7475 =
                   let uu____7477 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____7477  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____7475
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
    fun uu____7502  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____7502 with
          | (uvs,t) ->
              let uu____7515 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____7515 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____7527 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____7527 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____7545 =
                        let uu____7548 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____7548
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____7545)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7571 =
          let uu____7572 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7572 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7571 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7597 =
          let uu____7598 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7598 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7597 r
  
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
          (let uu____7647 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____7647
           then
             let uu____7650 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____7650
           else ());
          (let uu____7655 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____7655 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____7686 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____7686 FStar_List.flatten  in
               ((let uu____7700 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____7703 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____7703)
                    in
                 if uu____7700
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
                           let uu____7719 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____7729,uu____7730,uu____7731,uu____7732,uu____7733)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____7742 -> failwith "Impossible!"  in
                           match uu____7719 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Inductive type "
                                      (Prims.op_Hat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____7761 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____7771,uu____7772,ty_lid,uu____7774,uu____7775)
                               -> (data_lid, ty_lid)
                           | uu____7782 -> failwith "Impossible"  in
                         match uu____7761 with
                         | (data_lid,ty_lid) ->
                             let uu____7790 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____7793 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____7793)
                                in
                             if uu____7790
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Exception "
                                      (Prims.op_Hat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____7807 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____7812,uu____7813,uu____7814,uu____7815,uu____7816)
                         -> lid
                     | uu____7825 -> failwith "Impossible"  in
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
                   let uu____7843 =
                     (((FStar_List.length tcs) = Prims.int_zero) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____7843
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
          let pop1 uu____7918 =
            let uu____7919 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___1045_7929  ->
               match () with
               | () ->
                   let uu____7936 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____7936 (fun r  -> pop1 (); r)) ()
          with | uu___1044_7967 -> (pop1 (); FStar_Exn.raise uu___1044_7967)
  
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
      | uu____8283 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____8341 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____8341 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____8366 .
    'Auu____8366 FStar_Pervasives_Native.option -> 'Auu____8366 Prims.list
  =
  fun uu___0_8375  ->
    match uu___0_8375 with
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
            let uu____8455 = collect1 tl1  in
            (match uu____8455 with
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
        | ((e,n1)::uu____8693,[]) ->
            FStar_Pervasives_Native.Some (e, n1, Prims.int_zero)
        | ([],(e,n1)::uu____8749) ->
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
          let uu____8959 =
            let uu____8961 = FStar_Options.ide ()  in
            Prims.op_Negation uu____8961  in
          if uu____8959
          then
            let uu____8964 =
              let uu____8969 = FStar_TypeChecker_Env.dsenv env  in
              let uu____8970 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____8969 uu____8970  in
            (match uu____8964 with
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
                              let uu____9003 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____9004 =
                                let uu____9010 =
                                  let uu____9012 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____9014 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____9012 uu____9014
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____9010)
                                 in
                              FStar_Errors.log_issue uu____9003 uu____9004
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____9021 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____9022 =
                                   let uu____9028 =
                                     let uu____9030 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____9030
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____9028)
                                    in
                                 FStar_Errors.log_issue uu____9021 uu____9022)
                              else ())
                         else ())))
          else ()
      | uu____9040 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____9085 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____9113 ->
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
             let uu____9173 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____9173
             then
               let ses1 =
                 let uu____9181 =
                   let uu____9182 =
                     let uu____9183 =
                       tc_inductive
                         (let uu___1177_9192 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1177_9192.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1177_9192.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1177_9192.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1177_9192.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1177_9192.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1177_9192.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1177_9192.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1177_9192.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1177_9192.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1177_9192.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1177_9192.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1177_9192.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1177_9192.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1177_9192.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1177_9192.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1177_9192.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1177_9192.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1177_9192.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1177_9192.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1177_9192.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1177_9192.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___1177_9192.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1177_9192.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1177_9192.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1177_9192.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1177_9192.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1177_9192.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1177_9192.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1177_9192.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1177_9192.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1177_9192.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1177_9192.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1177_9192.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1177_9192.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1177_9192.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1177_9192.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1177_9192.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1177_9192.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1177_9192.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1177_9192.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1177_9192.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1177_9192.FStar_TypeChecker_Env.strict_args_tab)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____9183
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____9182
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____9181
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____9206 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____9206
                 then
                   let uu____9211 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1181_9215 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1181_9215.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1181_9215.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1181_9215.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1181_9215.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____9211
                 else ());
                ses1)
             else ses  in
           let uu____9225 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____9225 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___1188_9249 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1188_9249.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1188_9249.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1188_9249.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1188_9249.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____9261 = FStar_TypeChecker_DMFF.cps_and_elaborate env ne
              in
           (match uu____9261 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___1202_9300 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1202_9300.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1202_9300.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1202_9300.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1202_9300.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___1205_9302 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1205_9302.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1205_9302.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1205_9302.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1205_9302.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses), env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           ((let uu____9309 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "LayeredEffects")
                in
             if uu____9309
             then
               let uu____9314 = FStar_Syntax_Print.sigelt_to_string se  in
               FStar_Util.print1
                 "Starting to typecheck layered effect:\n%s\n" uu____9314
             else ());
            (let tc_fun =
               if ne.FStar_Syntax_Syntax.is_layered
               then tc_layered_eff_decl
               else tc_eff_decl  in
             let ne1 =
               let uu____9338 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env)
                  in
               if uu____9338
               then
                 let ne1 =
                   let uu____9342 =
                     let uu____9343 =
                       let uu____9344 =
                         tc_fun
                           (let uu___1215_9347 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1215_9347.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1215_9347.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1215_9347.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1215_9347.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1215_9347.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1215_9347.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1215_9347.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1215_9347.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1215_9347.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1215_9347.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1215_9347.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1215_9347.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1215_9347.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1215_9347.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1215_9347.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1215_9347.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1215_9347.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1215_9347.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1215_9347.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1215_9347.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1215_9347.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 = true;
                              FStar_TypeChecker_Env.failhard =
                                (uu___1215_9347.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1215_9347.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1215_9347.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1215_9347.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1215_9347.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1215_9347.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1215_9347.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1215_9347.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1215_9347.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1215_9347.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1215_9347.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1215_9347.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1215_9347.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1215_9347.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1215_9347.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1215_9347.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1215_9347.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1215_9347.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1215_9347.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1215_9347.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1215_9347.FStar_TypeChecker_Env.strict_args_tab)
                            }) ne
                          in
                       FStar_All.pipe_right uu____9344
                         (fun ne1  ->
                            let uu___1218_9353 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_new_effect ne1);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___1218_9353.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___1218_9353.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___1218_9353.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___1218_9353.FStar_Syntax_Syntax.sigattrs)
                            })
                        in
                     FStar_All.pipe_right uu____9343
                       (FStar_TypeChecker_Normalize.elim_uvars env)
                      in
                   FStar_All.pipe_right uu____9342
                     FStar_Syntax_Util.eff_decl_of_new_effect
                    in
                 ((let uu____9355 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "TwoPhases")
                      in
                   if uu____9355
                   then
                     let uu____9360 =
                       FStar_Syntax_Print.sigelt_to_string
                         (let uu___1222_9364 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1222_9364.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1222_9364.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1222_9364.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1222_9364.FStar_Syntax_Syntax.sigattrs)
                          })
                        in
                     FStar_Util.print1 "Effect decl after phase 1: %s\n"
                       uu____9360
                   else ());
                  ne1)
               else ne  in
             let ne2 = tc_fun env ne1  in
             let se1 =
               let uu___1227_9372 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_new_effect ne2);
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1227_9372.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1227_9372.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1227_9372.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1227_9372.FStar_Syntax_Syntax.sigattrs)
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
             ([(let uu___1236_9397 = se  in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                  FStar_Syntax_Syntax.sigrng =
                    (uu___1236_9397.FStar_Syntax_Syntax.sigrng);
                  FStar_Syntax_Syntax.sigquals =
                    (uu___1236_9397.FStar_Syntax_Syntax.sigquals);
                  FStar_Syntax_Syntax.sigmeta =
                    (uu___1236_9397.FStar_Syntax_Syntax.sigmeta);
                  FStar_Syntax_Syntax.sigattrs =
                    (uu___1236_9397.FStar_Syntax_Syntax.sigattrs)
                })], [], env0)
           else
             (let uu____9400 =
                let uu____9407 =
                  FStar_TypeChecker_Env.lookup_effect_lid env
                    sub1.FStar_Syntax_Syntax.source
                   in
                monad_signature env sub1.FStar_Syntax_Syntax.source
                  uu____9407
                 in
              match uu____9400 with
              | (a,wp_a_src) ->
                  let uu____9424 =
                    let uu____9431 =
                      FStar_TypeChecker_Env.lookup_effect_lid env
                        sub1.FStar_Syntax_Syntax.target
                       in
                    monad_signature env sub1.FStar_Syntax_Syntax.target
                      uu____9431
                     in
                  (match uu____9424 with
                   | (b,wp_b_tgt) ->
                       let wp_a_tgt =
                         let uu____9449 =
                           let uu____9452 =
                             let uu____9453 =
                               let uu____9460 =
                                 FStar_Syntax_Syntax.bv_to_name a  in
                               (b, uu____9460)  in
                             FStar_Syntax_Syntax.NT uu____9453  in
                           [uu____9452]  in
                         FStar_Syntax_Subst.subst uu____9449 wp_b_tgt  in
                       let expected_k =
                         let uu____9468 =
                           let uu____9477 = FStar_Syntax_Syntax.mk_binder a
                              in
                           let uu____9484 =
                             let uu____9493 =
                               FStar_Syntax_Syntax.null_binder wp_a_src  in
                             [uu____9493]  in
                           uu____9477 :: uu____9484  in
                         let uu____9518 =
                           FStar_Syntax_Syntax.mk_Total wp_a_tgt  in
                         FStar_Syntax_Util.arrow uu____9468 uu____9518  in
                       let repr_type eff_name a1 wp =
                         (let uu____9540 =
                            let uu____9542 =
                              FStar_TypeChecker_Env.is_reifiable_effect env
                                eff_name
                               in
                            Prims.op_Negation uu____9542  in
                          if uu____9540
                          then
                            let uu____9545 =
                              let uu____9551 =
                                FStar_Util.format1
                                  "Effect %s cannot be reified"
                                  eff_name.FStar_Ident.str
                                 in
                              (FStar_Errors.Fatal_EffectCannotBeReified,
                                uu____9551)
                               in
                            let uu____9555 =
                              FStar_TypeChecker_Env.get_range env  in
                            FStar_Errors.raise_error uu____9545 uu____9555
                          else ());
                         (let uu____9558 =
                            FStar_TypeChecker_Env.effect_decl_opt env
                              eff_name
                             in
                          match uu____9558 with
                          | FStar_Pervasives_Native.None  ->
                              failwith
                                "internal error: reifiable effect has no decl?"
                          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                              let repr =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [FStar_Syntax_Syntax.U_unknown] env ed
                                  ed.FStar_Syntax_Syntax.repr
                                 in
                              let uu____9591 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____9592 =
                                let uu____9599 =
                                  let uu____9600 =
                                    let uu____9617 =
                                      let uu____9628 =
                                        FStar_Syntax_Syntax.as_arg a1  in
                                      let uu____9637 =
                                        let uu____9648 =
                                          FStar_Syntax_Syntax.as_arg wp  in
                                        [uu____9648]  in
                                      uu____9628 :: uu____9637  in
                                    (repr, uu____9617)  in
                                  FStar_Syntax_Syntax.Tm_app uu____9600  in
                                FStar_Syntax_Syntax.mk uu____9599  in
                              uu____9592 FStar_Pervasives_Native.None
                                uu____9591)
                          in
                       let uu____9693 =
                         match ((sub1.FStar_Syntax_Syntax.lift),
                                 (sub1.FStar_Syntax_Syntax.lift_wp))
                         with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.None ) ->
                             failwith "Impossible (parser)"
                         | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp))
                             ->
                             let uu____9866 =
                               if (FStar_List.length uvs) > Prims.int_zero
                               then
                                 let uu____9877 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____9877 with
                                 | (usubst,uvs1) ->
                                     let uu____9900 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env uvs1
                                        in
                                     let uu____9901 =
                                       FStar_Syntax_Subst.subst usubst
                                         lift_wp
                                        in
                                     (uu____9900, uu____9901)
                               else (env, lift_wp)  in
                             (match uu____9866 with
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
                                       let uu____9951 =
                                         FStar_Syntax_Subst.close_univ_vars
                                           uvs lift_wp2
                                          in
                                       (uvs, uu____9951))
                                     in
                                  (lift, lift_wp2))
                         | (FStar_Pervasives_Native.Some
                            (what,lift),FStar_Pervasives_Native.None ) ->
                             let uu____10022 =
                               if (FStar_List.length what) > Prims.int_zero
                               then
                                 let uu____10037 =
                                   FStar_Syntax_Subst.univ_var_opening what
                                    in
                                 match uu____10037 with
                                 | (usubst,uvs) ->
                                     let uu____10062 =
                                       FStar_Syntax_Subst.subst usubst lift
                                        in
                                     (uvs, uu____10062)
                               else ([], lift)  in
                             (match uu____10022 with
                              | (uvs,lift1) ->
                                  ((let uu____10098 =
                                      FStar_TypeChecker_Env.debug env
                                        (FStar_Options.Other "ED")
                                       in
                                    if uu____10098
                                    then
                                      let uu____10102 =
                                        FStar_Syntax_Print.term_to_string
                                          lift1
                                         in
                                      FStar_Util.print1
                                        "Lift for free : %s\n" uu____10102
                                    else ());
                                   (let dmff_env =
                                      FStar_TypeChecker_DMFF.empty env
                                        (FStar_TypeChecker_TcTerm.tc_constant
                                           env FStar_Range.dummyRange)
                                       in
                                    let uu____10108 =
                                      let uu____10115 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env uvs
                                         in
                                      FStar_TypeChecker_TcTerm.tc_term
                                        uu____10115 lift1
                                       in
                                    match uu____10108 with
                                    | (lift2,comp,uu____10140) ->
                                        let uu____10141 =
                                          FStar_TypeChecker_DMFF.star_expr
                                            dmff_env lift2
                                           in
                                        (match uu____10141 with
                                         | (uu____10170,lift_wp,lift_elab) ->
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
                                               let uu____10202 =
                                                 let uu____10213 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env lift_elab1
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____10213
                                                  in
                                               let uu____10230 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_wp1
                                                  in
                                               (uu____10202, uu____10230)
                                             else
                                               (let uu____10259 =
                                                  let uu____10270 =
                                                    let uu____10279 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift_elab1
                                                       in
                                                    (uvs, uu____10279)  in
                                                  FStar_Pervasives_Native.Some
                                                    uu____10270
                                                   in
                                                let uu____10294 =
                                                  let uu____10303 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_wp1
                                                     in
                                                  (uvs, uu____10303)  in
                                                (uu____10259, uu____10294))))))
                          in
                       (match uu____9693 with
                        | (lift,lift_wp) ->
                            let env1 =
                              let uu___1307_10377 = env  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___1307_10377.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___1307_10377.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___1307_10377.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___1307_10377.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___1307_10377.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___1307_10377.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___1307_10377.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___1307_10377.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___1307_10377.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___1307_10377.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___1307_10377.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___1307_10377.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___1307_10377.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___1307_10377.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___1307_10377.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___1307_10377.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___1307_10377.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___1307_10377.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___1307_10377.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___1307_10377.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___1307_10377.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 =
                                  (uu___1307_10377.FStar_TypeChecker_Env.phase1);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___1307_10377.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___1307_10377.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___1307_10377.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___1307_10377.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___1307_10377.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___1307_10377.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___1307_10377.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___1307_10377.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___1307_10377.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___1307_10377.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___1307_10377.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___1307_10377.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___1307_10377.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___1307_10377.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___1307_10377.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___1307_10377.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___1307_10377.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___1307_10377.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___1307_10377.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___1307_10377.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___1307_10377.FStar_TypeChecker_Env.strict_args_tab)
                              }  in
                            let lift1 =
                              match lift with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None
                              | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                  let uu____10410 =
                                    let uu____10415 =
                                      FStar_Syntax_Subst.univ_var_opening uvs
                                       in
                                    match uu____10415 with
                                    | (usubst,uvs1) ->
                                        let uu____10438 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env1 uvs1
                                           in
                                        let uu____10439 =
                                          FStar_Syntax_Subst.subst usubst
                                            lift1
                                           in
                                        (uu____10438, uu____10439)
                                     in
                                  (match uu____10410 with
                                   | (env2,lift2) ->
                                       let uu____10444 =
                                         let uu____10451 =
                                           FStar_TypeChecker_Env.lookup_effect_lid
                                             env2
                                             sub1.FStar_Syntax_Syntax.source
                                            in
                                         monad_signature env2
                                           sub1.FStar_Syntax_Syntax.source
                                           uu____10451
                                          in
                                       (match uu____10444 with
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
                                                let uu____10477 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env2
                                                   in
                                                let uu____10478 =
                                                  let uu____10485 =
                                                    let uu____10486 =
                                                      let uu____10503 =
                                                        let uu____10514 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            a_typ
                                                           in
                                                        let uu____10523 =
                                                          let uu____10534 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              wp_a_typ
                                                             in
                                                          [uu____10534]  in
                                                        uu____10514 ::
                                                          uu____10523
                                                         in
                                                      (lift_wp1, uu____10503)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10486
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10485
                                                   in
                                                uu____10478
                                                  FStar_Pervasives_Native.None
                                                  uu____10477
                                                 in
                                              repr_type
                                                sub1.FStar_Syntax_Syntax.target
                                                a_typ lift_wp_a
                                               in
                                            let expected_k1 =
                                              let uu____10582 =
                                                let uu____10591 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a1
                                                   in
                                                let uu____10598 =
                                                  let uu____10607 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      wp_a
                                                     in
                                                  let uu____10614 =
                                                    let uu____10623 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        repr_f
                                                       in
                                                    [uu____10623]  in
                                                  uu____10607 :: uu____10614
                                                   in
                                                uu____10591 :: uu____10598
                                                 in
                                              let uu____10654 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  repr_result
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____10582 uu____10654
                                               in
                                            let uu____10657 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k1
                                               in
                                            (match uu____10657 with
                                             | (expected_k2,uu____10667,uu____10668)
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
                                                      let uu____10676 =
                                                        FStar_Syntax_Subst.close_univ_vars
                                                          uvs lift3
                                                         in
                                                      (uvs, uu____10676))
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   lift3)))
                               in
                            ((let uu____10684 =
                                let uu____10686 =
                                  let uu____10688 =
                                    FStar_All.pipe_right lift_wp
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10688
                                    FStar_List.length
                                   in
                                uu____10686 <> Prims.int_one  in
                              if uu____10684
                              then
                                let uu____10711 =
                                  let uu____10717 =
                                    let uu____10719 =
                                      FStar_Syntax_Print.lid_to_string
                                        sub1.FStar_Syntax_Syntax.source
                                       in
                                    let uu____10721 =
                                      FStar_Syntax_Print.lid_to_string
                                        sub1.FStar_Syntax_Syntax.target
                                       in
                                    let uu____10723 =
                                      let uu____10725 =
                                        let uu____10727 =
                                          FStar_All.pipe_right lift_wp
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____10727
                                          FStar_List.length
                                         in
                                      FStar_All.pipe_right uu____10725
                                        FStar_Util.string_of_int
                                       in
                                    FStar_Util.format3
                                      "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                      uu____10719 uu____10721 uu____10723
                                     in
                                  (FStar_Errors.Fatal_TooManyUniverse,
                                    uu____10717)
                                   in
                                FStar_Errors.raise_error uu____10711 r
                              else ());
                             (let uu____10754 =
                                (FStar_Util.is_some lift1) &&
                                  (let uu____10757 =
                                     let uu____10759 =
                                       let uu____10762 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10762
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10759
                                       FStar_List.length
                                      in
                                   uu____10757 <> Prims.int_one)
                                 in
                              if uu____10754
                              then
                                let uu____10801 =
                                  let uu____10807 =
                                    let uu____10809 =
                                      FStar_Syntax_Print.lid_to_string
                                        sub1.FStar_Syntax_Syntax.source
                                       in
                                    let uu____10811 =
                                      FStar_Syntax_Print.lid_to_string
                                        sub1.FStar_Syntax_Syntax.target
                                       in
                                    let uu____10813 =
                                      let uu____10815 =
                                        let uu____10817 =
                                          let uu____10820 =
                                            FStar_All.pipe_right lift1
                                              FStar_Util.must
                                             in
                                          FStar_All.pipe_right uu____10820
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____10817
                                          FStar_List.length
                                         in
                                      FStar_All.pipe_right uu____10815
                                        FStar_Util.string_of_int
                                       in
                                    FStar_Util.format3
                                      "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                      uu____10809 uu____10811 uu____10813
                                     in
                                  (FStar_Errors.Fatal_TooManyUniverse,
                                    uu____10807)
                                   in
                                FStar_Errors.raise_error uu____10801 r
                              else ());
                             (let sub2 =
                                let uu___1344_10863 = sub1  in
                                {
                                  FStar_Syntax_Syntax.source =
                                    (uu___1344_10863.FStar_Syntax_Syntax.source);
                                  FStar_Syntax_Syntax.target =
                                    (uu___1344_10863.FStar_Syntax_Syntax.target);
                                  FStar_Syntax_Syntax.lift_wp =
                                    (FStar_Pervasives_Native.Some lift_wp);
                                  FStar_Syntax_Syntax.lift = lift1
                                }  in
                              let se1 =
                                let uu___1347_10865 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1347_10865.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1347_10865.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1347_10865.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1347_10865.FStar_Syntax_Syntax.sigattrs)
                                }  in
                              ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let uu____10879 =
             if (FStar_List.length uvs) = Prims.int_zero
             then (env, uvs, tps, c)
             else
               (let uu____10907 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____10907 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____10938 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____10938 c  in
                    let uu____10947 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____10947, uvs1, tps1, c1))
              in
           (match uu____10879 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____10969 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____10969 with
                 | (tps2,c2) ->
                     let uu____10986 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____10986 with
                      | (tps3,env3,us) ->
                          let uu____11006 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____11006 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____11034)::uu____11035 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____11054 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____11062 =
                                   let uu____11064 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____11064  in
                                 if uu____11062
                                 then
                                   let uu____11067 =
                                     let uu____11073 =
                                       let uu____11075 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____11077 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____11075 uu____11077
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____11073)
                                      in
                                   FStar_Errors.raise_error uu____11067 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____11085 =
                                   let uu____11086 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____11086
                                    in
                                 match uu____11085 with
                                 | (uvs2,t) ->
                                     let uu____11117 =
                                       let uu____11122 =
                                         let uu____11135 =
                                           let uu____11136 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____11136.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____11135)  in
                                       match uu____11122 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____11151,c5)) -> ([], c5)
                                       | (uu____11193,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____11232 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____11117 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               Prims.int_one
                                           then
                                             (let uu____11266 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____11266 with
                                              | (uu____11271,t1) ->
                                                  let uu____11273 =
                                                    let uu____11279 =
                                                      let uu____11281 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____11283 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____11287 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____11281
                                                        uu____11283
                                                        uu____11287
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____11279)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____11273 r)
                                           else ();
                                           (let se1 =
                                              let uu___1417_11294 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___1417_11294.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___1417_11294.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___1417_11294.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___1417_11294.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____11301,uu____11302,uu____11303) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_11308  ->
                   match uu___1_11308 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____11311 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____11317,uu____11318) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_11327  ->
                   match uu___1_11327 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____11330 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____11341 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____11341
             then
               let uu____11344 =
                 let uu____11350 =
                   let uu____11352 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____11352
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____11350)
                  in
               FStar_Errors.raise_error uu____11344 r
             else ());
            (let uu____11358 =
               let uu____11367 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____11367
               then
                 let uu____11378 =
                   tc_declare_typ
                     (let uu___1441_11381 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1441_11381.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1441_11381.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1441_11381.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1441_11381.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1441_11381.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1441_11381.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1441_11381.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1441_11381.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1441_11381.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1441_11381.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1441_11381.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1441_11381.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1441_11381.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1441_11381.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1441_11381.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1441_11381.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1441_11381.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1441_11381.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1441_11381.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1441_11381.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1441_11381.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1441_11381.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1441_11381.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1441_11381.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1441_11381.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1441_11381.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1441_11381.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1441_11381.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1441_11381.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1441_11381.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1441_11381.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1441_11381.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1441_11381.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1441_11381.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1441_11381.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1441_11381.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1441_11381.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1441_11381.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1441_11381.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1441_11381.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___1441_11381.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___1441_11381.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1441_11381.FStar_TypeChecker_Env.strict_args_tab)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____11378 with
                 | (uvs1,t1) ->
                     ((let uu____11406 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____11406
                       then
                         let uu____11411 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____11413 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____11411 uu____11413
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____11358 with
             | (uvs1,t1) ->
                 let uu____11448 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____11448 with
                  | (uvs2,t2) ->
                      ([(let uu___1454_11478 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1454_11478.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1454_11478.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1454_11478.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1454_11478.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____11483 =
             let uu____11492 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____11492
             then
               let uu____11503 =
                 tc_assume
                   (let uu___1463_11506 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1463_11506.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1463_11506.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1463_11506.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1463_11506.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1463_11506.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1463_11506.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1463_11506.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1463_11506.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1463_11506.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1463_11506.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1463_11506.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1463_11506.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1463_11506.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1463_11506.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1463_11506.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1463_11506.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1463_11506.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1463_11506.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1463_11506.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1463_11506.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1463_11506.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___1463_11506.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1463_11506.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1463_11506.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1463_11506.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1463_11506.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1463_11506.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1463_11506.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1463_11506.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1463_11506.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1463_11506.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1463_11506.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1463_11506.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1463_11506.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1463_11506.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1463_11506.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1463_11506.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1463_11506.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1463_11506.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1463_11506.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1463_11506.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1463_11506.FStar_TypeChecker_Env.strict_args_tab)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____11503 with
               | (uvs1,t1) ->
                   ((let uu____11532 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____11532
                     then
                       let uu____11537 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____11539 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____11537
                         uu____11539
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____11483 with
            | (uvs1,t1) ->
                let uu____11574 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____11574 with
                 | (uvs2,t2) ->
                     ([(let uu___1476_11604 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1476_11604.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1476_11604.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1476_11604.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1476_11604.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____11608 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____11608 with
            | (e1,c,g1) ->
                let uu____11628 =
                  let uu____11635 = FStar_TypeChecker_Common.lcomp_comp c  in
                  match uu____11635 with
                  | (c1,g_lc) ->
                      let uu____11648 =
                        let uu____11655 =
                          let uu____11658 =
                            FStar_Syntax_Util.ml_comp
                              FStar_Syntax_Syntax.t_unit r
                             in
                          FStar_Pervasives_Native.Some uu____11658  in
                        FStar_TypeChecker_TcTerm.check_expected_effect env2
                          uu____11655 (e1, c1)
                         in
                      (match uu____11648 with
                       | (e2,_x,g) ->
                           let uu____11668 =
                             FStar_TypeChecker_Env.conj_guard g_lc g  in
                           (e2, _x, uu____11668))
                   in
                (match uu____11628 with
                 | (e2,uu____11680,g) ->
                     ((let uu____11683 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____11683);
                      (let se1 =
                         let uu___1498_11685 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1498_11685.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1498_11685.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1498_11685.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1498_11685.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____11697 = FStar_Options.debug_any ()  in
             if uu____11697
             then
               let uu____11700 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____11702 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____11700
                 uu____11702
             else ());
            (let uu____11707 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____11707 with
             | (t1,uu____11725,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____11739 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____11739 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____11742 =
                              let uu____11748 =
                                let uu____11750 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____11752 =
                                  let uu____11754 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____11754
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____11750 uu____11752
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____11748)
                               in
                            FStar_Errors.raise_error uu____11742 r
                        | uu____11766 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___1519_11771 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1519_11771.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1519_11771.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1519_11771.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1519_11771.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1519_11771.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1519_11771.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1519_11771.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1519_11771.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1519_11771.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1519_11771.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1519_11771.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1519_11771.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1519_11771.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1519_11771.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1519_11771.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1519_11771.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1519_11771.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1519_11771.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1519_11771.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1519_11771.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___1519_11771.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1519_11771.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1519_11771.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1519_11771.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1519_11771.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1519_11771.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1519_11771.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1519_11771.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1519_11771.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1519_11771.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1519_11771.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1519_11771.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1519_11771.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1519_11771.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1519_11771.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1519_11771.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1519_11771.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1519_11771.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1519_11771.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1519_11771.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1519_11771.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___1519_11771.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1519_11771.FStar_TypeChecker_Env.strict_args_tab)
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
                 let uu____11839 =
                   let uu____11841 =
                     let uu____11850 = drop_logic val_q  in
                     let uu____11853 = drop_logic q'  in
                     (uu____11850, uu____11853)  in
                   match uu____11841 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____11839
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____11880 =
                      let uu____11886 =
                        let uu____11888 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____11890 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____11892 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____11888 uu____11890 uu____11892
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____11886)
                       in
                    FStar_Errors.raise_error uu____11880 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____11929 =
                   let uu____11930 = FStar_Syntax_Subst.compress def  in
                   uu____11930.FStar_Syntax_Syntax.n  in
                 match uu____11929 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____11942,uu____11943) -> binders
                 | uu____11968 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____11980;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____12085) -> val_bs1
                     | (uu____12116,[]) -> val_bs1
                     | ((body_bv,uu____12148)::bt,(val_bv,aqual)::vt) ->
                         let uu____12205 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____12229) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___1588_12243 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___1590_12246 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___1590_12246.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___1588_12243.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1588_12243.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____12205
                      in
                   let uu____12253 =
                     let uu____12260 =
                       let uu____12261 =
                         let uu____12276 = rename_binders1 def_bs val_bs  in
                         (uu____12276, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____12261  in
                     FStar_Syntax_Syntax.mk uu____12260  in
                   uu____12253 FStar_Pervasives_Native.None r1
               | uu____12295 -> typ1  in
             let uu___1596_12296 = lb  in
             let uu____12297 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___1596_12296.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1596_12296.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____12297;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1596_12296.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___1596_12296.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1596_12296.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1596_12296.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____12300 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____12355  ->
                     fun lb  ->
                       match uu____12355 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____12401 =
                             let uu____12413 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____12413 with
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
                                   | uu____12493 ->
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
                                  (let uu____12540 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____12540, quals_opt1)))
                              in
                           (match uu____12401 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____12300 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____12644 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___2_12650  ->
                                match uu___2_12650 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____12655 -> false))
                         in
                      if uu____12644
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____12668 =
                    let uu____12675 =
                      let uu____12676 =
                        let uu____12690 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____12690)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____12676  in
                    FStar_Syntax_Syntax.mk uu____12675  in
                  uu____12668 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___1639_12709 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1639_12709.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1639_12709.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1639_12709.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1639_12709.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1639_12709.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1639_12709.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1639_12709.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1639_12709.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1639_12709.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1639_12709.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1639_12709.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1639_12709.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1639_12709.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1639_12709.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1639_12709.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1639_12709.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1639_12709.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1639_12709.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1639_12709.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1639_12709.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1639_12709.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1639_12709.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1639_12709.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1639_12709.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1639_12709.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1639_12709.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1639_12709.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1639_12709.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1639_12709.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1639_12709.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1639_12709.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1639_12709.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1639_12709.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1639_12709.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1639_12709.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1639_12709.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1639_12709.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1639_12709.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1639_12709.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1639_12709.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1639_12709.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___1639_12709.FStar_TypeChecker_Env.strict_args_tab)
                  }  in
                let e1 =
                  let uu____12712 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____12712
                  then
                    let drop_lbtyp e_lax =
                      let uu____12721 =
                        let uu____12722 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____12722.FStar_Syntax_Syntax.n  in
                      match uu____12721 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____12744 =
                              let uu____12745 = FStar_Syntax_Subst.compress e
                                 in
                              uu____12745.FStar_Syntax_Syntax.n  in
                            match uu____12744 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____12749,lb1::[]),uu____12751) ->
                                let uu____12767 =
                                  let uu____12768 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____12768.FStar_Syntax_Syntax.n  in
                                (match uu____12767 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____12773 -> false)
                            | uu____12775 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___1664_12779 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___1666_12794 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___1666_12794.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___1666_12794.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___1666_12794.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___1666_12794.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___1666_12794.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___1666_12794.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___1664_12779.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___1664_12779.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____12797 -> e_lax  in
                    let uu____12798 =
                      FStar_Util.record_time
                        (fun uu____12806  ->
                           let uu____12807 =
                             let uu____12808 =
                               let uu____12809 =
                                 FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                   (let uu___1670_12818 = env'  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___1670_12818.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___1670_12818.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___1670_12818.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___1670_12818.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___1670_12818.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___1670_12818.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___1670_12818.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___1670_12818.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___1670_12818.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___1670_12818.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___1670_12818.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___1670_12818.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___1670_12818.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___1670_12818.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___1670_12818.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___1670_12818.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___1670_12818.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___1670_12818.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___1670_12818.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___1670_12818.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___1670_12818.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___1670_12818.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___1670_12818.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___1670_12818.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___1670_12818.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___1670_12818.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___1670_12818.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___1670_12818.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___1670_12818.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___1670_12818.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___1670_12818.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___1670_12818.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___1670_12818.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___1670_12818.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___1670_12818.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___1670_12818.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___1670_12818.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___1670_12818.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___1670_12818.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___1670_12818.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___1670_12818.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___1670_12818.FStar_TypeChecker_Env.strict_args_tab)
                                    }) e
                                  in
                               FStar_All.pipe_right uu____12809
                                 (fun uu____12831  ->
                                    match uu____12831 with
                                    | (e1,uu____12839,uu____12840) -> e1)
                                in
                             FStar_All.pipe_right uu____12808
                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                  env')
                              in
                           FStar_All.pipe_right uu____12807 drop_lbtyp)
                       in
                    match uu____12798 with
                    | (e1,ms) ->
                        ((let uu____12846 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TwoPhases")
                             in
                          if uu____12846
                          then
                            let uu____12851 =
                              FStar_Syntax_Print.term_to_string e1  in
                            FStar_Util.print1
                              "Let binding after phase 1: %s\n" uu____12851
                          else ());
                         (let uu____12857 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TCDeclTime")
                             in
                          if uu____12857
                          then
                            let uu____12862 = FStar_Util.string_of_int ms  in
                            FStar_Util.print1
                              "Let binding elaborated (phase 1) in %s milliseconds\n"
                              uu____12862
                          else ());
                         e1)
                  else e  in
                let uu____12869 =
                  let uu____12878 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____12878 with
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
                (match uu____12869 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___1700_12983 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___1700_12983.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1700_12983.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1700_12983.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1700_12983.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___1707_12996 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1707_12996.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1707_12996.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___1707_12996.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___1707_12996.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1707_12996.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1707_12996.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____12997 =
                       FStar_Util.record_time
                         (fun uu____13016  ->
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              env' e1)
                        in
                     (match uu____12997 with
                      | (r1,ms) ->
                          ((let uu____13044 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TCDeclTime")
                               in
                            if uu____13044
                            then
                              let uu____13049 = FStar_Util.string_of_int ms
                                 in
                              FStar_Util.print1
                                "Let binding typechecked in phase 2 in %s milliseconds\n"
                                uu____13049
                            else ());
                           (let uu____13054 =
                              match r1 with
                              | ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                                   FStar_Syntax_Syntax.pos = uu____13079;
                                   FStar_Syntax_Syntax.vars = uu____13080;_},uu____13081,g)
                                  when FStar_TypeChecker_Env.is_trivial g ->
                                  let lbs2 =
                                    let uu____13111 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.snd lbs1)
                                        (FStar_List.map rename_parameters)
                                       in
                                    ((FStar_Pervasives_Native.fst lbs1),
                                      uu____13111)
                                     in
                                  let lbs3 =
                                    let uu____13135 =
                                      match post_tau with
                                      | FStar_Pervasives_Native.Some tau ->
                                          FStar_List.map (postprocess_lb tau)
                                            (FStar_Pervasives_Native.snd lbs2)
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.snd lbs2
                                       in
                                    ((FStar_Pervasives_Native.fst lbs2),
                                      uu____13135)
                                     in
                                  let quals1 =
                                    match e2.FStar_Syntax_Syntax.n with
                                    | FStar_Syntax_Syntax.Tm_meta
                                        (uu____13158,FStar_Syntax_Syntax.Meta_desugared
                                         (FStar_Syntax_Syntax.Masked_effect
                                         ))
                                        ->
                                        FStar_Syntax_Syntax.HasMaskedEffect
                                        :: quals
                                    | uu____13163 -> quals  in
                                  ((let uu___1737_13172 = se1  in
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_let
                                           (lbs3, lids));
                                      FStar_Syntax_Syntax.sigrng =
                                        (uu___1737_13172.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals = quals1;
                                      FStar_Syntax_Syntax.sigmeta =
                                        (uu___1737_13172.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (uu___1737_13172.FStar_Syntax_Syntax.sigattrs)
                                    }), lbs3)
                              | uu____13175 ->
                                  failwith
                                    "impossible (typechecking should preserve Tm_let)"
                               in
                            match uu____13054 with
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
                                 (let uu____13231 = log env1  in
                                  if uu____13231
                                  then
                                    let uu____13234 =
                                      let uu____13236 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.snd lbs1)
                                          (FStar_List.map
                                             (fun lb  ->
                                                let should_log =
                                                  let uu____13256 =
                                                    let uu____13265 =
                                                      let uu____13266 =
                                                        let uu____13269 =
                                                          FStar_Util.right
                                                            lb.FStar_Syntax_Syntax.lbname
                                                           in
                                                        uu____13269.FStar_Syntax_Syntax.fv_name
                                                         in
                                                      uu____13266.FStar_Syntax_Syntax.v
                                                       in
                                                    FStar_TypeChecker_Env.try_lookup_val_decl
                                                      env1 uu____13265
                                                     in
                                                  match uu____13256 with
                                                  | FStar_Pervasives_Native.None
                                                       -> true
                                                  | uu____13278 -> false  in
                                                if should_log
                                                then
                                                  let uu____13290 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  let uu____13292 =
                                                    FStar_Syntax_Print.term_to_string
                                                      lb.FStar_Syntax_Syntax.lbtyp
                                                     in
                                                  FStar_Util.format2
                                                    "let %s : %s" uu____13290
                                                    uu____13292
                                                else ""))
                                         in
                                      FStar_All.pipe_right uu____13236
                                        (FStar_String.concat "\n")
                                       in
                                    FStar_Util.print1 "%s\n" uu____13234
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
      (let uu____13344 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____13344
       then
         let uu____13347 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____13347
       else ());
      (let uu____13352 = get_fail_se se  in
       match uu____13352 with
       | FStar_Pervasives_Native.Some (uu____13373,false ) when
           let uu____13390 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____13390 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___1768_13416 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___1768_13416.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___1768_13416.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___1768_13416.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___1768_13416.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___1768_13416.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___1768_13416.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___1768_13416.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___1768_13416.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___1768_13416.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___1768_13416.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___1768_13416.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___1768_13416.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___1768_13416.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___1768_13416.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___1768_13416.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___1768_13416.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___1768_13416.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___1768_13416.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___1768_13416.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___1768_13416.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___1768_13416.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___1768_13416.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___1768_13416.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___1768_13416.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___1768_13416.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___1768_13416.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___1768_13416.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___1768_13416.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___1768_13416.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___1768_13416.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___1768_13416.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___1768_13416.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___1768_13416.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___1768_13416.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___1768_13416.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___1768_13416.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___1768_13416.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___1768_13416.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___1768_13416.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___1768_13416.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___1768_13416.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___1768_13416.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___1768_13416.FStar_TypeChecker_Env.strict_args_tab)
               }
             else env1  in
           ((let uu____13421 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____13421
             then
               let uu____13424 =
                 let uu____13426 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____13426
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____13424
             else ());
            (let uu____13440 =
               FStar_Errors.catch_errors
                 (fun uu____13470  ->
                    FStar_Options.with_saved_options
                      (fun uu____13482  -> tc_decl' env' se))
                in
             match uu____13440 with
             | (errs,uu____13494) ->
                 ((let uu____13524 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____13524
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____13559 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____13559  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____13571 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____13582 =
                            let uu____13592 = check_multi_eq errnos1 actual
                               in
                            match uu____13592 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- Prims.int_one), (~- Prims.int_one),
                                  (~- Prims.int_one))
                             in
                          (match uu____13582 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____13657 =
                                   let uu____13663 =
                                     let uu____13665 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____13668 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____13671 =
                                       FStar_Util.string_of_int e  in
                                     let uu____13673 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____13675 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____13665 uu____13668 uu____13671
                                       uu____13673 uu____13675
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____13663)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____13657)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____13702 .
    'Auu____13702 ->
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
               (fun uu___3_13745  ->
                  match uu___3_13745 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____13748 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____13759) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____13767 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____13777 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____13782 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____13798 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____13824 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13850) ->
            let uu____13859 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13859
            then
              let for_export_bundle se1 uu____13896 =
                match uu____13896 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____13935,uu____13936) ->
                         let dec =
                           let uu___1844_13946 = se1  in
                           let uu____13947 =
                             let uu____13948 =
                               let uu____13955 =
                                 let uu____13956 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____13956  in
                               (l, us, uu____13955)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____13948
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____13947;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1844_13946.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1844_13946.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1844_13946.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____13966,uu____13967,uu____13968) ->
                         let dec =
                           let uu___1855_13976 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1855_13976.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1855_13976.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1855_13976.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____13981 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____14004,uu____14005,uu____14006) ->
            let uu____14007 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____14007 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____14031 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____14031
            then
              ([(let uu___1871_14050 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___1871_14050.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___1871_14050.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___1871_14050.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____14053 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_14059  ->
                         match uu___4_14059 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____14062 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____14068 ->
                             true
                         | uu____14070 -> false))
                  in
               if uu____14053 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____14091 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____14096 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14101 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____14106 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14111 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____14129) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____14143 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____14143
            then ([], hidden)
            else
              (let dec =
                 let uu____14164 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____14164;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____14175 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____14175
            then
              let uu____14186 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1908_14200 = se  in
                        let uu____14201 =
                          let uu____14202 =
                            let uu____14209 =
                              let uu____14210 =
                                let uu____14213 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____14213.FStar_Syntax_Syntax.fv_name  in
                              uu____14210.FStar_Syntax_Syntax.v  in
                            (uu____14209, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____14202  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____14201;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1908_14200.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1908_14200.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1908_14200.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____14186, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____14236 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____14236
       then
         let uu____14239 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____14239
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____14244 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____14262 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
           uu____14279) ->
           let env1 =
             let uu___1929_14284 = env  in
             let uu____14285 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1929_14284.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1929_14284.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1929_14284.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1929_14284.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1929_14284.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1929_14284.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1929_14284.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1929_14284.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1929_14284.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1929_14284.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1929_14284.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1929_14284.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1929_14284.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1929_14284.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1929_14284.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1929_14284.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1929_14284.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1929_14284.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1929_14284.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1929_14284.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1929_14284.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1929_14284.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1929_14284.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1929_14284.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1929_14284.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1929_14284.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1929_14284.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1929_14284.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1929_14284.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1929_14284.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1929_14284.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1929_14284.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1929_14284.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1929_14284.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14285;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1929_14284.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1929_14284.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1929_14284.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1929_14284.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1929_14284.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1929_14284.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1929_14284.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1929_14284.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1929_14284.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
           let env1 =
             let uu___1929_14287 = env  in
             let uu____14288 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1929_14287.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1929_14287.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1929_14287.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1929_14287.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1929_14287.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1929_14287.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1929_14287.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1929_14287.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1929_14287.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1929_14287.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1929_14287.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1929_14287.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1929_14287.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1929_14287.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1929_14287.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1929_14287.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1929_14287.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1929_14287.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1929_14287.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1929_14287.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1929_14287.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1929_14287.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1929_14287.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1929_14287.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1929_14287.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1929_14287.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1929_14287.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1929_14287.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1929_14287.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1929_14287.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1929_14287.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1929_14287.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1929_14287.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1929_14287.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14288;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1929_14287.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1929_14287.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1929_14287.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1929_14287.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1929_14287.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1929_14287.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1929_14287.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1929_14287.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1929_14287.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions
           uu____14289) ->
           let env1 =
             let uu___1929_14292 = env  in
             let uu____14293 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1929_14292.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1929_14292.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1929_14292.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1929_14292.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1929_14292.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1929_14292.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1929_14292.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1929_14292.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1929_14292.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1929_14292.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1929_14292.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1929_14292.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1929_14292.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1929_14292.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1929_14292.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1929_14292.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1929_14292.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1929_14292.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1929_14292.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1929_14292.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1929_14292.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1929_14292.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1929_14292.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1929_14292.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1929_14292.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1929_14292.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1929_14292.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1929_14292.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1929_14292.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1929_14292.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1929_14292.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1929_14292.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1929_14292.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1929_14292.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14293;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1929_14292.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1929_14292.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1929_14292.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1929_14292.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1929_14292.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1929_14292.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1929_14292.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1929_14292.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1929_14292.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____14294) ->
           let env1 =
             let uu___1929_14299 = env  in
             let uu____14300 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1929_14299.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1929_14299.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1929_14299.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1929_14299.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1929_14299.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1929_14299.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1929_14299.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1929_14299.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1929_14299.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1929_14299.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1929_14299.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1929_14299.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1929_14299.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1929_14299.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1929_14299.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1929_14299.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1929_14299.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1929_14299.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1929_14299.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1929_14299.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1929_14299.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1929_14299.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1929_14299.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1929_14299.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1929_14299.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1929_14299.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1929_14299.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1929_14299.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1929_14299.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1929_14299.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1929_14299.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1929_14299.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1929_14299.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1929_14299.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14300;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1929_14299.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1929_14299.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1929_14299.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1929_14299.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1929_14299.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1929_14299.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1929_14299.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1929_14299.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1929_14299.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver )
           ->
           ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
              ();
            env)
       | FStar_Syntax_Syntax.Sig_pragma uu____14302 -> env
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14303 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____14313 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____14313) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____14314,uu____14315,uu____14316) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_14321  ->
                   match uu___5_14321 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____14324 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____14326,uu____14327) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_14336  ->
                   match uu___5_14336 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____14339 -> false))
           -> env
       | uu____14341 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____14410 se =
        match uu____14410 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____14463 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____14463
              then
                let uu____14466 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____14466
              else ());
             (let uu____14471 = tc_decl env1 se  in
              match uu____14471 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____14524 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____14524
                             then
                               let uu____14528 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____14528
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____14544 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____14544
                             then
                               let uu____14548 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____14548
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
                    (let uu____14565 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____14565
                     then
                       let uu____14570 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____14579 =
                                  let uu____14581 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____14581 "\n"  in
                                Prims.op_Hat s uu____14579) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____14570
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____14591 =
                       let uu____14600 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____14600
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____14642 se1 =
                            match uu____14642 with
                            | (exports1,hidden1) ->
                                let uu____14670 = for_export env3 hidden1 se1
                                   in
                                (match uu____14670 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____14591 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____14824 = acc  in
        match uu____14824 with
        | (uu____14859,uu____14860,env1,uu____14862) ->
            let r =
              let uu____14896 =
                let uu____14900 =
                  let uu____14902 = FStar_TypeChecker_Env.current_module env1
                     in
                  FStar_Ident.string_of_lid uu____14902  in
                FStar_Pervasives_Native.Some uu____14900  in
              FStar_Profiling.profile
                (fun uu____14925  -> process_one_decl acc se) uu____14896
                "FStar.TypeChecker.Tc.process_one_decl"
               in
            ((let uu____14928 = FStar_Options.profile_group_by_decls ()  in
              if uu____14928
              then
                let tag =
                  match FStar_Syntax_Util.lids_of_sigelt se with
                  | hd1::uu____14935 -> FStar_Ident.string_of_lid hd1
                  | uu____14938 ->
                      FStar_Range.string_of_range
                        (FStar_Syntax_Util.range_of_sigelt se)
                   in
                FStar_Profiling.report_and_clear tag
              else ());
             r)
         in
      let uu____14943 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____14943 with
      | (ses1,exports,env1,uu____14991) ->
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
          let uu___2029_15029 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2029_15029.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2029_15029.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2029_15029.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2029_15029.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2029_15029.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2029_15029.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2029_15029.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2029_15029.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2029_15029.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2029_15029.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___2029_15029.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___2029_15029.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___2029_15029.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2029_15029.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2029_15029.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___2029_15029.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2029_15029.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___2029_15029.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2029_15029.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___2029_15029.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___2029_15029.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___2029_15029.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2029_15029.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2029_15029.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2029_15029.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2029_15029.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2029_15029.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2029_15029.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2029_15029.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2029_15029.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2029_15029.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2029_15029.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2029_15029.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2029_15029.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___2029_15029.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2029_15029.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2029_15029.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2029_15029.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2029_15029.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2029_15029.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2029_15029.FStar_TypeChecker_Env.strict_args_tab)
          }  in
        let check_term lid univs1 t =
          let uu____15049 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____15049 with
          | (univs2,t1) ->
              ((let uu____15057 =
                  let uu____15059 =
                    let uu____15065 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____15065  in
                  FStar_All.pipe_left uu____15059
                    (FStar_Options.Other "Exports")
                   in
                if uu____15057
                then
                  let uu____15069 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____15071 =
                    let uu____15073 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____15073
                      (FStar_String.concat ", ")
                     in
                  let uu____15090 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____15069 uu____15071 uu____15090
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____15096 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____15096 (fun a1  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____15122 =
             let uu____15124 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____15126 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____15124 uu____15126
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____15122);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15137) ->
              let uu____15146 =
                let uu____15148 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15148  in
              if uu____15146
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____15162,uu____15163) ->
              let t =
                let uu____15175 =
                  let uu____15182 =
                    let uu____15183 =
                      let uu____15198 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____15198)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____15183  in
                  FStar_Syntax_Syntax.mk uu____15182  in
                uu____15175 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____15214,uu____15215,uu____15216) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____15226 =
                let uu____15228 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15228  in
              if uu____15226 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____15236,lbs),uu____15238) ->
              let uu____15249 =
                let uu____15251 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15251  in
              if uu____15249
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
              let uu____15274 =
                let uu____15276 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15276  in
              if uu____15274
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____15297 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____15298 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____15305 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15306 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____15307 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____15308 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____15315 -> ()  in
        let uu____15316 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____15316 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____15422) -> true
             | uu____15424 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____15454 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____15493 ->
                   let uu____15494 =
                     let uu____15501 =
                       let uu____15502 =
                         let uu____15517 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____15517)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____15502  in
                     FStar_Syntax_Syntax.mk uu____15501  in
                   uu____15494 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____15534,uu____15535) ->
            let s1 =
              let uu___2155_15545 = s  in
              let uu____15546 =
                let uu____15547 =
                  let uu____15554 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____15554)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____15547  in
              let uu____15555 =
                let uu____15558 =
                  let uu____15561 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____15561  in
                FStar_Syntax_Syntax.Assumption :: uu____15558  in
              {
                FStar_Syntax_Syntax.sigel = uu____15546;
                FStar_Syntax_Syntax.sigrng =
                  (uu___2155_15545.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____15555;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2155_15545.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___2155_15545.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____15564 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____15589 lbdef =
        match uu____15589 with
        | (uvs,t) ->
            let attrs =
              let uu____15600 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____15600
              then
                let uu____15605 =
                  let uu____15606 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____15606
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____15605 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___2168_15609 = s  in
            let uu____15610 =
              let uu____15613 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____15613  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___2168_15609.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____15610;
              FStar_Syntax_Syntax.sigmeta =
                (uu___2168_15609.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____15631 -> failwith "Impossible!"  in
        let c_opt =
          let uu____15638 = FStar_Syntax_Util.is_unit t  in
          if uu____15638
          then
            let uu____15645 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____15645
          else
            (let uu____15652 =
               let uu____15653 = FStar_Syntax_Subst.compress t  in
               uu____15653.FStar_Syntax_Syntax.n  in
             match uu____15652 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____15660,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____15684 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____15696 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____15696
            then false
            else
              (let uu____15703 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____15703
               then true
               else
                 (let uu____15710 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____15710))
         in
      let extract_sigelt s =
        (let uu____15722 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____15722
         then
           let uu____15725 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____15725
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____15732 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____15752 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____15771 ->
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
                             (lid,uu____15817,uu____15818,uu____15819,uu____15820,uu____15821)
                             ->
                             ((let uu____15831 =
                                 let uu____15834 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____15834  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____15831);
                              (let uu____15883 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____15883 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____15887,uu____15888,uu____15889,uu____15890,uu____15891)
                             ->
                             ((let uu____15899 =
                                 let uu____15902 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____15902  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____15899);
                              sigelts1)
                         | uu____15951 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____15960 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15960
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____15970 =
                    let uu___2232_15971 = s  in
                    let uu____15972 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2232_15971.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2232_15971.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15972;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2232_15971.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2232_15971.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15970])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____15983 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15983
             then []
             else
               (let uu____15990 = lbs  in
                match uu____15990 with
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
                        (fun uu____16052  ->
                           match uu____16052 with
                           | (uu____16060,t,uu____16062) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____16079  ->
                             match uu____16079 with
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
                           (fun uu____16106  ->
                              match uu____16106 with
                              | (uu____16114,t,uu____16116) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____16128,uu____16129) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____16137 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____16166 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____16166) uu____16137
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____16170 =
                    let uu___2274_16171 = s  in
                    let uu____16172 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2274_16171.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2274_16171.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____16172;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2274_16171.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2274_16171.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____16170]
                else [])
             else
               (let uu____16179 =
                  let uu___2276_16180 = s  in
                  let uu____16181 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___2276_16180.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___2276_16180.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____16181;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___2276_16180.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___2276_16180.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____16179])
         | FStar_Syntax_Syntax.Sig_new_effect uu____16184 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____16185 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____16186 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____16187 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____16200 -> [s])
         in
      let uu___2288_16201 = m  in
      let uu____16202 =
        let uu____16203 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____16203 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___2288_16201.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____16202;
        FStar_Syntax_Syntax.exports =
          (uu___2288_16201.FStar_Syntax_Syntax.exports);
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
        (fun uu____16254  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____16301  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____16316 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____16316
  
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
      (let uu____16405 = FStar_Options.debug_any ()  in
       if uu____16405
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
         let uu___2313_16421 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___2313_16421.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___2313_16421.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___2313_16421.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___2313_16421.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___2313_16421.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___2313_16421.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___2313_16421.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___2313_16421.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___2313_16421.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___2313_16421.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___2313_16421.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___2313_16421.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___2313_16421.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___2313_16421.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___2313_16421.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___2313_16421.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___2313_16421.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___2313_16421.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___2313_16421.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___2313_16421.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___2313_16421.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___2313_16421.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___2313_16421.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___2313_16421.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___2313_16421.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___2313_16421.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___2313_16421.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___2313_16421.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___2313_16421.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___2313_16421.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___2313_16421.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___2313_16421.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___2313_16421.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___2313_16421.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___2313_16421.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___2313_16421.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___2313_16421.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___2313_16421.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___2313_16421.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___2313_16421.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___2313_16421.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___2313_16421.FStar_TypeChecker_Env.strict_args_tab)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____16423 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____16423 with
       | (ses,exports,env3) ->
           ((let uu___2321_16456 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___2321_16456.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___2321_16456.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___2321_16456.FStar_Syntax_Syntax.is_interface)
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
        let uu____16485 = tc_decls env decls  in
        match uu____16485 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___2330_16516 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___2330_16516.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___2330_16516.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___2330_16516.FStar_Syntax_Syntax.is_interface)
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
        let uu____16577 = tc_partial_modul env01 m  in
        match uu____16577 with
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
                (let uu____16614 = FStar_Errors.get_err_count ()  in
                 uu____16614 = Prims.int_zero)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____16625 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____16625
                then
                  let uu____16629 =
                    let uu____16631 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16631 then "" else " (in lax mode) "  in
                  let uu____16639 =
                    let uu____16641 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16641
                    then
                      let uu____16645 =
                        let uu____16647 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.op_Hat uu____16647 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____16645
                    else ""  in
                  let uu____16654 =
                    let uu____16656 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16656
                    then
                      let uu____16660 =
                        let uu____16662 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____16662 "\n"  in
                      Prims.op_Hat "\nto: " uu____16660
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____16629
                    uu____16639 uu____16654
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___2356_16676 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2356_16676.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2356_16676.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2356_16676.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2356_16676.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2356_16676.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2356_16676.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2356_16676.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2356_16676.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2356_16676.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2356_16676.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2356_16676.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2356_16676.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2356_16676.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2356_16676.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2356_16676.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2356_16676.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2356_16676.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2356_16676.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2356_16676.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2356_16676.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2356_16676.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2356_16676.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2356_16676.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2356_16676.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2356_16676.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2356_16676.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2356_16676.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2356_16676.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2356_16676.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2356_16676.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2356_16676.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___2356_16676.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2356_16676.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2356_16676.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2356_16676.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2356_16676.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2356_16676.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2356_16676.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2356_16676.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2356_16676.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2356_16676.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2356_16676.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2356_16676.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let en02 =
                    let uu___2359_16678 = en01  in
                    let uu____16679 =
                      let uu____16694 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____16694, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2359_16678.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2359_16678.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2359_16678.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2359_16678.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2359_16678.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2359_16678.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2359_16678.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2359_16678.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2359_16678.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2359_16678.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2359_16678.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2359_16678.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2359_16678.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2359_16678.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2359_16678.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2359_16678.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2359_16678.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2359_16678.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2359_16678.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2359_16678.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2359_16678.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2359_16678.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2359_16678.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2359_16678.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2359_16678.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2359_16678.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2359_16678.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2359_16678.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2359_16678.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2359_16678.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2359_16678.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____16679;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2359_16678.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2359_16678.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2359_16678.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2359_16678.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2359_16678.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2359_16678.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2359_16678.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2359_16678.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2359_16678.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___2359_16678.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2359_16678.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2359_16678.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let uu____16740 =
                    let uu____16742 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____16742  in
                  if uu____16740
                  then
                    ((let uu____16746 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____16746 (fun a2  -> ()));
                     en02)
                  else en02  in
                let uu____16750 = tc_modul en0 modul_iface true  in
                match uu____16750 with
                | (modul_iface1,env) ->
                    ((let uu___2368_16763 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___2368_16763.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___2368_16763.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___2368_16763.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___2370_16767 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___2370_16767.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___2370_16767.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___2370_16767.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____16770 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____16770 FStar_Util.smap_clear);
               (let uu____16806 =
                  ((let uu____16810 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____16810) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____16813 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____16813)
                   in
                if uu____16806 then check_exports env modul exports else ());
               (let uu____16819 =
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____16819 (fun a3  -> ()));
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
        let uu____16834 =
          let uu____16836 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____16836  in
        push_context env uu____16834  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____16857 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____16868 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____16868 with | (uu____16875,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____16900 = FStar_Options.debug_any ()  in
         if uu____16900
         then
           let uu____16903 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____16903
         else ());
        (let uu____16915 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____16915
         then
           let uu____16918 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____16918
         else ());
        (let env1 =
           let uu___2400_16924 = env  in
           let uu____16925 =
             let uu____16927 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____16927  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___2400_16924.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___2400_16924.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___2400_16924.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___2400_16924.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___2400_16924.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___2400_16924.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___2400_16924.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___2400_16924.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___2400_16924.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___2400_16924.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___2400_16924.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___2400_16924.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___2400_16924.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___2400_16924.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___2400_16924.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___2400_16924.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___2400_16924.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___2400_16924.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___2400_16924.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___2400_16924.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____16925;
             FStar_TypeChecker_Env.lax_universes =
               (uu___2400_16924.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___2400_16924.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___2400_16924.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___2400_16924.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___2400_16924.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___2400_16924.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___2400_16924.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___2400_16924.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___2400_16924.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___2400_16924.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___2400_16924.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___2400_16924.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___2400_16924.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___2400_16924.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___2400_16924.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___2400_16924.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___2400_16924.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___2400_16924.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___2400_16924.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___2400_16924.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___2400_16924.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___2400_16924.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___2400_16924.FStar_TypeChecker_Env.strict_args_tab)
           }  in
         let uu____16929 = tc_modul env1 m b  in
         match uu____16929 with
         | (m1,env2) ->
             ((let uu____16941 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____16941
               then
                 let uu____16944 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____16944
               else ());
              (let uu____16950 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____16950
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
                         let uu____16988 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____16988 with
                         | (univnames1,e) ->
                             let uu___2422_16995 = lb  in
                             let uu____16996 =
                               let uu____16999 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____16999 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2422_16995.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2422_16995.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___2422_16995.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2422_16995.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16996;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2422_16995.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2422_16995.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___2424_17000 = se  in
                       let uu____17001 =
                         let uu____17002 =
                           let uu____17009 =
                             let uu____17010 = FStar_List.map update lbs  in
                             (b1, uu____17010)  in
                           (uu____17009, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____17002  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____17001;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___2424_17000.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___2424_17000.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___2424_17000.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___2424_17000.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____17018 -> se  in
                 let normalized_module =
                   let uu___2428_17020 = m1  in
                   let uu____17021 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___2428_17020.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____17021;
                     FStar_Syntax_Syntax.exports =
                       (uu___2428_17020.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___2428_17020.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____17022 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____17022
               else ());
              (m1, env2)))
  