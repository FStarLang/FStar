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
  
let (tc_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      (let uu____452 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____452
       then
         let uu____457 = FStar_Syntax_Print.eff_decl_to_string false ed  in
         FStar_Util.print1 "Typechecking layered effect: \n\t%s\n" uu____457
       else ());
      if
        ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
          ||
          ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
             Prims.int_zero)
      then
        (let uu____475 =
           FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname  in
         FStar_Errors.raise_error
           (FStar_Errors.Fatal_UnexpectedEffect,
             (Prims.op_Hat "Binders are not supported for layered effects ("
                (Prims.op_Hat (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                   ")"))) uu____475)
      else ();
      (let check_and_gen' comb n1 env_opt uu____515 =
         match uu____515 with
         | (us,t) ->
             let env =
               if FStar_Util.is_some env_opt
               then FStar_All.pipe_right env_opt FStar_Util.must
               else env0  in
             let uu____544 = FStar_Syntax_Subst.open_univ_vars us t  in
             (match uu____544 with
              | (us1,t1) ->
                  let uu____557 =
                    let uu____562 =
                      let uu____569 =
                        FStar_TypeChecker_Env.push_univ_vars env us1  in
                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term uu____569
                        t1
                       in
                    match uu____562 with
                    | (t2,lc,g) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (t2, (lc.FStar_Syntax_Syntax.res_typ)))
                     in
                  (match uu____557 with
                   | (t2,ty) ->
                       let uu____586 =
                         FStar_TypeChecker_Util.generalize_universes env t2
                          in
                       (match uu____586 with
                        | (g_us,t3) ->
                            let ty1 =
                              FStar_Syntax_Subst.close_univ_vars g_us ty  in
                            (if (FStar_List.length g_us) <> n1
                             then
                               (let error =
                                  let uu____609 = FStar_Util.string_of_int n1
                                     in
                                  let uu____611 =
                                    let uu____613 =
                                      FStar_All.pipe_right g_us
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____613
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format4
                                    "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                    comb uu____609 uu____611
                                   in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                    error) t3.FStar_Syntax_Syntax.pos)
                             else ();
                             (match us1 with
                              | [] -> (g_us, t3, ty1)
                              | uu____630 ->
                                  let uu____631 =
                                    ((FStar_List.length us1) =
                                       (FStar_List.length g_us))
                                      &&
                                      (FStar_List.forall2
                                         (fun u1  ->
                                            fun u2  ->
                                              let uu____638 =
                                                FStar_Syntax_Syntax.order_univ_name
                                                  u1 u2
                                                 in
                                              uu____638 = Prims.int_zero) us1
                                         g_us)
                                     in
                                  if uu____631
                                  then (g_us, t3, ty1)
                                  else
                                    (let uu____651 =
                                       let uu____657 =
                                         let uu____659 =
                                           FStar_Util.string_of_int
                                             (FStar_List.length us1)
                                            in
                                         let uu____661 =
                                           FStar_Util.string_of_int
                                             (FStar_List.length g_us)
                                            in
                                         FStar_Util.format4
                                           "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                           (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                           comb uu____659 uu____661
                                          in
                                       (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                         uu____657)
                                        in
                                     FStar_Errors.raise_error uu____651
                                       t3.FStar_Syntax_Syntax.pos))))))
          in
       let log_combinator s uu____694 =
         match uu____694 with
         | (us,t,ty) ->
             let uu____723 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                 (FStar_Options.Other "LayeredEffects")
                in
             if uu____723
             then
               let uu____728 = FStar_Syntax_Print.tscheme_to_string (us, t)
                  in
               let uu____734 = FStar_Syntax_Print.tscheme_to_string (us, ty)
                  in
               FStar_Util.print4 "Typechecked %s:%s = %s:%s\n"
                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str s uu____728
                 uu____734
             else ()
          in
       let fresh_a_and_u_a a =
         let uu____755 = FStar_Syntax_Util.type_u ()  in
         FStar_All.pipe_right uu____755
           (fun uu____772  ->
              match uu____772 with
              | (t,u) ->
                  let uu____783 =
                    let uu____784 =
                      FStar_Syntax_Syntax.gen_bv a
                        FStar_Pervasives_Native.None t
                       in
                    FStar_All.pipe_right uu____784
                      FStar_Syntax_Syntax.mk_binder
                     in
                  (uu____783, u))
          in
       let fresh_x_a x a =
         let uu____798 =
           let uu____799 =
             let uu____800 =
               FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
             FStar_All.pipe_right uu____800 FStar_Syntax_Syntax.bv_to_name
              in
           FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
             uu____799
            in
         FStar_All.pipe_right uu____798 FStar_Syntax_Syntax.mk_binder  in
       let signature =
         let r =
           (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
            in
         let uu____827 =
           check_and_gen' "signature" Prims.int_one
             FStar_Pervasives_Native.None ed.FStar_Syntax_Syntax.signature
            in
         match uu____827 with
         | (sig_us,sig_t,sig_ty) ->
             let uu____851 = FStar_Syntax_Subst.open_univ_vars sig_us sig_t
                in
             (match uu____851 with
              | (us,t) ->
                  let env = FStar_TypeChecker_Env.push_univ_vars env0 us  in
                  let uu____871 = fresh_a_and_u_a "a"  in
                  (match uu____871 with
                   | (a,uu____890) ->
                       let rest_bs =
                         let uu____900 =
                           let uu____901 = FStar_Syntax_Subst.compress t  in
                           uu____901.FStar_Syntax_Syntax.n  in
                         match uu____900 with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,uu____913) when
                             (FStar_List.length bs) >= Prims.int_one ->
                             let uu____941 =
                               FStar_Syntax_Subst.open_binders bs  in
                             (match uu____941 with
                              | (a',uu____951)::bs1 ->
                                  let substs =
                                    let uu____974 =
                                      let uu____975 =
                                        let uu____982 =
                                          FStar_Syntax_Syntax.bv_to_name
                                            (FStar_Pervasives_Native.fst a)
                                           in
                                        (a', uu____982)  in
                                      FStar_Syntax_Syntax.NT uu____975  in
                                    [uu____974]  in
                                  FStar_Syntax_Subst.subst_binders substs bs1
                              | uu____989 -> failwith "Impossible!")
                         | uu____999 ->
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_UnexpectedEffect, "") r
                          in
                       let bs = a :: rest_bs  in
                       let k =
                         let uu____1028 =
                           FStar_Syntax_Syntax.mk_Total
                             FStar_Syntax_Syntax.teff
                            in
                         FStar_Syntax_Util.arrow bs uu____1028  in
                       let g_eq = FStar_TypeChecker_Rel.teq env t k  in
                       (FStar_TypeChecker_Rel.force_trivial_guard env g_eq;
                        (let uu____1033 =
                           let uu____1036 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Env.Beta] env k
                              in
                           FStar_Syntax_Subst.close_univ_vars us uu____1036
                            in
                         (sig_us, uu____1033, sig_ty)))))
          in
       log_combinator "signature" signature;
       (let repr =
          let r =
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.pos
             in
          let uu____1063 =
            check_and_gen' "repr" Prims.int_one FStar_Pervasives_Native.None
              ed.FStar_Syntax_Syntax.repr
             in
          match uu____1063 with
          | (repr_us,repr_t,repr_ty) ->
              let uu____1087 =
                FStar_Syntax_Subst.open_univ_vars repr_us repr_ty  in
              (match uu____1087 with
               | (us,ty) ->
                   let env = FStar_TypeChecker_Env.push_univ_vars env0 us  in
                   let uu____1107 = fresh_a_and_u_a "a"  in
                   (match uu____1107 with
                    | (a,uu____1126) ->
                        let rest_bs =
                          let signature_ts =
                            let uu____1137 = signature  in
                            match uu____1137 with
                            | (us1,t,uu____1152) -> (us1, t)  in
                          let uu____1169 =
                            FStar_TypeChecker_Env.inst_tscheme signature_ts
                             in
                          match uu____1169 with
                          | (uu____1182,signature1) ->
                              let uu____1184 =
                                let uu____1185 =
                                  FStar_Syntax_Subst.compress signature1  in
                                uu____1185.FStar_Syntax_Syntax.n  in
                              (match uu____1184 with
                               | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1197)
                                   ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   (match bs1 with
                                    | (a',uu____1228)::bs2 ->
                                        let substs =
                                          let uu____1251 =
                                            let uu____1252 =
                                              let uu____1259 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  (FStar_Pervasives_Native.fst
                                                     a)
                                                 in
                                              (a', uu____1259)  in
                                            FStar_Syntax_Syntax.NT uu____1252
                                             in
                                          [uu____1251]  in
                                        FStar_Syntax_Subst.subst_binders
                                          substs bs2
                                    | uu____1266 -> failwith "Impossible!")
                               | uu____1276 -> failwith "Impossible!")
                           in
                        let bs = a :: rest_bs  in
                        let k =
                          let uu____1304 =
                            let uu____1307 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_right uu____1307
                              (fun uu____1319  ->
                                 match uu____1319 with
                                 | (t,u) ->
                                     FStar_Syntax_Syntax.mk_Total' t
                                       (FStar_Pervasives_Native.Some u))
                             in
                          FStar_Syntax_Util.arrow bs uu____1304  in
                        let g = FStar_TypeChecker_Rel.teq env ty k  in
                        (FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (let uu____1328 =
                            let uu____1331 =
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Env.Beta] env k
                               in
                            FStar_Syntax_Subst.close_univ_vars us uu____1331
                             in
                          (repr_us, repr_t, uu____1328)))))
           in
        log_combinator "repr" repr;
        (let fresh_repr r env u a_tm =
           let signature1 =
             let uu____1374 = signature  in
             match uu____1374 with | (us,t,uu____1389) -> (us, t)  in
           let fail1 t =
             let uu____1416 =
               FStar_TypeChecker_Err.unexpected_signature_for_monad env0
                 ed.FStar_Syntax_Syntax.mname t
                in
             FStar_Errors.raise_error uu____1416
               (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
              in
           let uu____1430 = FStar_TypeChecker_Env.inst_tscheme signature1  in
           match uu____1430 with
           | (uu____1439,signature2) ->
               let uu____1441 =
                 let uu____1442 = FStar_Syntax_Subst.compress signature2  in
                 uu____1442.FStar_Syntax_Syntax.n  in
               (match uu____1441 with
                | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1450) ->
                    let bs1 = FStar_Syntax_Subst.open_binders bs  in
                    (match bs1 with
                     | a::bs2 ->
                         let uu____1498 =
                           FStar_List.fold_left
                             (fun uu____1537  ->
                                fun uu____1538  ->
                                  match (uu____1537, uu____1538) with
                                  | ((is,g,substs),(b,uu____1585)) ->
                                      let uu____1614 =
                                        let uu____1627 =
                                          FStar_Syntax_Subst.subst substs
                                            b.FStar_Syntax_Syntax.sort
                                           in
                                        FStar_TypeChecker_Util.new_implicit_var
                                          "" r env uu____1627
                                         in
                                      (match uu____1614 with
                                       | (t,uu____1640,g_t) ->
                                           let uu____1654 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g g_t
                                              in
                                           ((FStar_List.append is [t]),
                                             uu____1654,
                                             (FStar_List.append substs
                                                [FStar_Syntax_Syntax.NT
                                                   (b, t)]))))
                             ([], FStar_TypeChecker_Env.trivial_guard,
                               [FStar_Syntax_Syntax.NT
                                  ((FStar_Pervasives_Native.fst a), a_tm)])
                             bs2
                            in
                         (match uu____1498 with
                          | (is,g,uu____1675) ->
                              let repr_ts =
                                let uu____1685 = repr  in
                                match uu____1685 with
                                | (us,t,uu____1700) -> (us, t)  in
                              let repr1 =
                                let uu____1718 =
                                  FStar_TypeChecker_Env.inst_tscheme_with
                                    repr_ts [u]
                                   in
                                FStar_All.pipe_right uu____1718
                                  FStar_Pervasives_Native.snd
                                 in
                              let uu____1727 =
                                let uu____1728 =
                                  let uu____1733 =
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      (a_tm :: is)
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app repr1
                                    uu____1733
                                   in
                                uu____1728 FStar_Pervasives_Native.None r  in
                              (uu____1727, g))
                     | uu____1742 -> fail1 signature2)
                | uu____1743 -> fail1 signature2)
            in
         let return_repr =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
              in
           let uu____1762 =
             check_and_gen' "return_repr" Prims.int_one
               FStar_Pervasives_Native.None
               ed.FStar_Syntax_Syntax.return_repr
              in
           match uu____1762 with
           | (ret_us,ret_t,ret_ty) ->
               let uu____1786 =
                 FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
               (match uu____1786 with
                | (us,ty) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                       in
                    let uu____1806 = fresh_a_and_u_a "a"  in
                    (match uu____1806 with
                     | (a,u_a) ->
                         let x_a = fresh_x_a "x" a  in
                         let rest_bs =
                           let uu____1837 =
                             let uu____1838 = FStar_Syntax_Subst.compress ty
                                in
                             uu____1838.FStar_Syntax_Syntax.n  in
                           match uu____1837 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1850)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____1878 =
                                 FStar_Syntax_Subst.open_binders bs  in
                               (match uu____1878 with
                                | (a',uu____1888)::(x_a',uu____1890)::bs1 ->
                                    let substs =
                                      let uu____1923 =
                                        let uu____1924 =
                                          let uu____1931 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              (FStar_Pervasives_Native.fst a)
                                             in
                                          (a', uu____1931)  in
                                        FStar_Syntax_Syntax.NT uu____1924  in
                                      let uu____1938 =
                                        let uu____1941 =
                                          let uu____1942 =
                                            let uu____1949 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   x_a)
                                               in
                                            (x_a', uu____1949)  in
                                          FStar_Syntax_Syntax.NT uu____1942
                                           in
                                        [uu____1941]  in
                                      uu____1923 :: uu____1938  in
                                    FStar_Syntax_Subst.subst_binders substs
                                      bs1
                                | uu____1956 -> failwith "Impossible!")
                           | uu____1966 ->
                               FStar_Errors.raise_error
                                 (FStar_Errors.Fatal_UnexpectedEffect, "") r
                            in
                         let bs = a :: x_a :: rest_bs  in
                         let uu____1998 =
                           let uu____2003 =
                             FStar_TypeChecker_Env.push_binders env bs  in
                           let uu____2004 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.fst a)
                               FStar_Syntax_Syntax.bv_to_name
                              in
                           fresh_repr r uu____2003 u_a uu____2004  in
                         (match uu____1998 with
                          | (repr1,g) ->
                              let k =
                                let uu____2028 =
                                  FStar_Syntax_Syntax.mk_Total' repr1
                                    (FStar_Pervasives_Native.Some u_a)
                                   in
                                FStar_Syntax_Util.arrow bs uu____2028  in
                              let g_eq = FStar_TypeChecker_Rel.teq env ty k
                                 in
                              ((let uu____2033 =
                                  FStar_TypeChecker_Env.conj_guard g g_eq  in
                                FStar_TypeChecker_Rel.force_trivial_guard env
                                  uu____2033);
                               (let uu____2034 =
                                  let uu____2037 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env k
                                     in
                                  FStar_Syntax_Subst.close_univ_vars us
                                    uu____2037
                                   in
                                (ret_us, ret_t, uu____2034))))))
            in
         log_combinator "return_repr" return_repr;
         (let bind_repr =
            let r =
              (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
               in
            let uu____2064 =
              check_and_gen' "bind_repr" (Prims.of_int (2))
                FStar_Pervasives_Native.None ed.FStar_Syntax_Syntax.bind_repr
               in
            match uu____2064 with
            | (bind_us,bind_t,bind_ty) ->
                let uu____2088 =
                  FStar_Syntax_Subst.open_univ_vars bind_us bind_ty  in
                (match uu____2088 with
                 | (us,ty) ->
                     let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                        in
                     let uu____2108 = fresh_a_and_u_a "a"  in
                     (match uu____2108 with
                      | (a,u_a) ->
                          let uu____2128 = fresh_a_and_u_a "b"  in
                          (match uu____2128 with
                           | (b,u_b) ->
                               let rest_bs =
                                 let uu____2157 =
                                   let uu____2158 =
                                     FStar_Syntax_Subst.compress ty  in
                                   uu____2158.FStar_Syntax_Syntax.n  in
                                 match uu____2157 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____2170) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (4))
                                     ->
                                     let uu____2198 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____2198 with
                                      | (a',uu____2208)::(b',uu____2210)::bs1
                                          ->
                                          let uu____2240 =
                                            FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 (Prims.of_int (2))) bs1
                                             in
                                          (match uu____2240 with
                                           | (bs2,uu____2283) ->
                                               let substs =
                                                 let uu____2319 =
                                                   let uu____2320 =
                                                     let uu____2327 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a)
                                                        in
                                                     (a', uu____2327)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____2320
                                                    in
                                                 let uu____2334 =
                                                   let uu____2337 =
                                                     let uu____2338 =
                                                       let uu____2345 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              b)
                                                          in
                                                       (b', uu____2345)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____2338
                                                      in
                                                   [uu____2337]  in
                                                 uu____2319 :: uu____2334  in
                                               FStar_Syntax_Subst.subst_binders
                                                 substs bs2)
                                      | uu____2352 -> failwith "Impossible!")
                                 | uu____2362 ->
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_UnexpectedEffect,
                                         "") r
                                  in
                               let bs = a :: b :: rest_bs  in
                               let uu____2394 =
                                 let uu____2405 =
                                   let uu____2410 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____2411 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____2410 u_a uu____2411  in
                                 match uu____2405 with
                                 | (repr1,g) ->
                                     let uu____2430 =
                                       let uu____2437 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None repr1
                                          in
                                       FStar_All.pipe_right uu____2437
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____2430, g)
                                  in
                               (match uu____2394 with
                                | (f,g_f) ->
                                    let uu____2477 =
                                      let x_a = fresh_x_a "x" a  in
                                      let uu____2490 =
                                        let uu____2495 =
                                          FStar_TypeChecker_Env.push_binders
                                            env (FStar_List.append bs [x_a])
                                           in
                                        let uu____2514 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst b)
                                            FStar_Syntax_Syntax.bv_to_name
                                           in
                                        fresh_repr r uu____2495 u_b
                                          uu____2514
                                         in
                                      match uu____2490 with
                                      | (repr1,g) ->
                                          let uu____2533 =
                                            let uu____2540 =
                                              let uu____2541 =
                                                let uu____2542 =
                                                  FStar_Syntax_Syntax.mk_Total'
                                                    repr1
                                                    (FStar_Pervasives_Native.Some
                                                       u_b)
                                                   in
                                                FStar_Syntax_Util.arrow 
                                                  [x_a] uu____2542
                                                 in
                                              FStar_Syntax_Syntax.gen_bv "g"
                                                FStar_Pervasives_Native.None
                                                uu____2541
                                               in
                                            FStar_All.pipe_right uu____2540
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          (uu____2533, g)
                                       in
                                    (match uu____2477 with
                                     | (g,g_g) ->
                                         let uu____2596 =
                                           let uu____2601 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____2602 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst b)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____2601 u_b
                                             uu____2602
                                            in
                                         (match uu____2596 with
                                          | (repr1,g_repr) ->
                                              let k =
                                                let uu____2626 =
                                                  FStar_Syntax_Syntax.mk_Total'
                                                    repr1
                                                    (FStar_Pervasives_Native.Some
                                                       u_b)
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  (FStar_List.append bs
                                                     [f; g]) uu____2626
                                                 in
                                              let g_eq =
                                                FStar_TypeChecker_Rel.teq env
                                                  ty k
                                                 in
                                              (FStar_List.iter
                                                 (FStar_TypeChecker_Rel.force_trivial_guard
                                                    env)
                                                 [g_f; g_g; g_repr; g_eq];
                                               (let uu____2655 =
                                                  let uu____2658 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Beta]
                                                      env k
                                                     in
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    bind_us uu____2658
                                                   in
                                                (bind_us, bind_t, uu____2655)))))))))
             in
          log_combinator "bind_repr" bind_repr;
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
             (let uu____2692 =
                let uu____2697 =
                  FStar_Syntax_Subst.univ_var_opening
                    act.FStar_Syntax_Syntax.action_univs
                   in
                match uu____2697 with
                | (usubst,us) ->
                    let uu____2720 =
                      FStar_TypeChecker_Env.push_univ_vars env us  in
                    let uu____2721 =
                      let uu___352_2722 = act  in
                      let uu____2723 =
                        FStar_Syntax_Subst.subst usubst
                          act.FStar_Syntax_Syntax.action_defn
                         in
                      let uu____2724 =
                        FStar_Syntax_Subst.subst usubst
                          act.FStar_Syntax_Syntax.action_typ
                         in
                      {
                        FStar_Syntax_Syntax.action_name =
                          (uu___352_2722.FStar_Syntax_Syntax.action_name);
                        FStar_Syntax_Syntax.action_unqualified_name =
                          (uu___352_2722.FStar_Syntax_Syntax.action_unqualified_name);
                        FStar_Syntax_Syntax.action_univs = us;
                        FStar_Syntax_Syntax.action_params =
                          (uu___352_2722.FStar_Syntax_Syntax.action_params);
                        FStar_Syntax_Syntax.action_defn = uu____2723;
                        FStar_Syntax_Syntax.action_typ = uu____2724
                      }  in
                    (uu____2720, uu____2721)
                 in
              match uu____2692 with
              | (env1,act1) ->
                  let act_typ =
                    let uu____2728 =
                      let uu____2729 =
                        FStar_Syntax_Subst.compress
                          act1.FStar_Syntax_Syntax.action_typ
                         in
                      uu____2729.FStar_Syntax_Syntax.n  in
                    match uu____2728 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
                        let uu____2755 =
                          FStar_Ident.lid_equals
                            ct.FStar_Syntax_Syntax.effect_name
                            ed.FStar_Syntax_Syntax.mname
                           in
                        if uu____2755
                        then
                          let repr_ts =
                            let uu____2759 = repr  in
                            match uu____2759 with
                            | (us,t,uu____2774) -> (us, t)  in
                          let repr1 =
                            let uu____2792 =
                              FStar_TypeChecker_Env.inst_tscheme_with repr_ts
                                ct.FStar_Syntax_Syntax.comp_univs
                               in
                            FStar_All.pipe_right uu____2792
                              FStar_Pervasives_Native.snd
                             in
                          let c1 =
                            let uu____2804 =
                              let uu____2805 =
                                let uu____2810 =
                                  let uu____2811 =
                                    FStar_Syntax_Syntax.as_arg
                                      ct.FStar_Syntax_Syntax.result_typ
                                     in
                                  uu____2811 ::
                                    (ct.FStar_Syntax_Syntax.effect_args)
                                   in
                                FStar_Syntax_Syntax.mk_Tm_app repr1
                                  uu____2810
                                 in
                              uu____2805 FStar_Pervasives_Native.None r  in
                            FStar_All.pipe_right uu____2804
                              FStar_Syntax_Syntax.mk_Total
                             in
                          FStar_Syntax_Util.arrow bs c1
                        else act1.FStar_Syntax_Syntax.action_typ
                    | uu____2832 -> act1.FStar_Syntax_Syntax.action_typ  in
                  let uu____2833 =
                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 act_typ
                     in
                  (match uu____2833 with
                   | (act_typ1,uu____2841,g_t) ->
                       let uu____2843 =
                         let uu____2850 =
                           let uu___376_2851 =
                             FStar_TypeChecker_Env.set_expected_typ env1
                               act_typ1
                              in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___376_2851.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___376_2851.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___376_2851.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___376_2851.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___376_2851.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___376_2851.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___376_2851.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___376_2851.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___376_2851.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___376_2851.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___376_2851.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp = false;
                             FStar_TypeChecker_Env.effects =
                               (uu___376_2851.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___376_2851.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___376_2851.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___376_2851.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___376_2851.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___376_2851.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___376_2851.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___376_2851.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___376_2851.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___376_2851.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___376_2851.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___376_2851.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___376_2851.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___376_2851.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___376_2851.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___376_2851.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___376_2851.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___376_2851.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___376_2851.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___376_2851.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___376_2851.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___376_2851.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___376_2851.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___376_2851.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___376_2851.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___376_2851.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___376_2851.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___376_2851.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___376_2851.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___376_2851.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___376_2851.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___376_2851.FStar_TypeChecker_Env.strict_args_tab)
                           }  in
                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                           uu____2850 act1.FStar_Syntax_Syntax.action_defn
                          in
                       (match uu____2843 with
                        | (act_defn,uu____2854,g_d) ->
                            ((let uu____2857 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "LayeredEffects")
                                 in
                              if uu____2857
                              then
                                let uu____2862 =
                                  FStar_Syntax_Print.term_to_string act_defn
                                   in
                                let uu____2864 =
                                  FStar_Syntax_Print.term_to_string act_typ1
                                   in
                                FStar_Util.print2
                                  "Typechecked action definition: %s and action type: %s\n"
                                  uu____2862 uu____2864
                              else ());
                             (let uu____2869 =
                                let act_typ2 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta] env1
                                    act_typ1
                                   in
                                let uu____2877 =
                                  let uu____2878 =
                                    FStar_Syntax_Subst.compress act_typ2  in
                                  uu____2878.FStar_Syntax_Syntax.n  in
                                match uu____2877 with
                                | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                    let bs1 =
                                      FStar_Syntax_Subst.open_binders bs  in
                                    let env2 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs1
                                       in
                                    let uu____2911 =
                                      FStar_Syntax_Util.type_u ()  in
                                    (match uu____2911 with
                                     | (t,u) ->
                                         let uu____2924 =
                                           FStar_TypeChecker_Util.new_implicit_var
                                             "" r env2 t
                                            in
                                         (match uu____2924 with
                                          | (a_tm,uu____2945,g_tm) ->
                                              let uu____2959 =
                                                fresh_repr r env2 u a_tm  in
                                              (match uu____2959 with
                                               | (repr1,g) ->
                                                   let uu____2972 =
                                                     let uu____2975 =
                                                       let uu____2978 =
                                                         let uu____2981 =
                                                           FStar_TypeChecker_Env.new_u_univ
                                                             ()
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____2981
                                                           (fun _2984  ->
                                                              FStar_Pervasives_Native.Some
                                                                _2984)
                                                          in
                                                       FStar_Syntax_Syntax.mk_Total'
                                                         repr1 uu____2978
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       bs1 uu____2975
                                                      in
                                                   let uu____2985 =
                                                     FStar_TypeChecker_Env.conj_guard
                                                       g g_tm
                                                      in
                                                   (uu____2972, uu____2985))))
                                | uu____2988 ->
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                        "") r
                                 in
                              match uu____2869 with
                              | (k,g_k) ->
                                  ((let uu____3004 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other "LayeredEffects")
                                       in
                                    if uu____3004
                                    then
                                      let uu____3009 =
                                        FStar_Syntax_Print.term_to_string k
                                         in
                                      FStar_Util.print1
                                        "Expected action type: %s\n"
                                        uu____3009
                                    else ());
                                   (let g =
                                      FStar_TypeChecker_Rel.teq env1 act_typ1
                                        k
                                       in
                                    FStar_List.iter
                                      (FStar_TypeChecker_Rel.force_trivial_guard
                                         env1) [g_t; g_d; g_k; g];
                                    (let uu____3017 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other
                                            "LayeredEffects")
                                        in
                                     if uu____3017
                                     then
                                       let uu____3022 =
                                         FStar_Syntax_Print.term_to_string k
                                          in
                                       FStar_Util.print1
                                         "Expected action type after unification: %s\n"
                                         uu____3022
                                     else ());
                                    (let act_typ2 =
                                       let repr_args t =
                                         let uu____3046 =
                                           let uu____3047 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____3047.FStar_Syntax_Syntax.n
                                            in
                                         match uu____3046 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (head1,a::is) ->
                                             let uu____3099 =
                                               let uu____3100 =
                                                 FStar_Syntax_Subst.compress
                                                   head1
                                                  in
                                               uu____3100.FStar_Syntax_Syntax.n
                                                in
                                             (match uu____3099 with
                                              | FStar_Syntax_Syntax.Tm_uinst
                                                  (uu____3109,us) ->
                                                  (us,
                                                    (FStar_Pervasives_Native.fst
                                                       a), is)
                                              | uu____3119 ->
                                                  failwith "Impossible!")
                                         | uu____3127 ->
                                             failwith "Impossible!"
                                          in
                                       let k1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Env.Beta] env1
                                           k
                                          in
                                       let uu____3136 =
                                         let uu____3137 =
                                           FStar_Syntax_Subst.compress k1  in
                                         uu____3137.FStar_Syntax_Syntax.n  in
                                       match uu____3136 with
                                       | FStar_Syntax_Syntax.Tm_arrow 
                                           (bs,c) ->
                                           let uu____3162 =
                                             FStar_Syntax_Subst.open_comp bs
                                               c
                                              in
                                           (match uu____3162 with
                                            | (bs1,c1) ->
                                                let uu____3169 =
                                                  repr_args
                                                    (FStar_Syntax_Util.comp_result
                                                       c1)
                                                   in
                                                (match uu____3169 with
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
                                                     let uu____3180 =
                                                       FStar_Syntax_Syntax.mk_Comp
                                                         ct
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       bs1 uu____3180))
                                       | uu____3183 -> failwith "Impossible!"
                                        in
                                     (let uu____3186 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____3186
                                      then
                                        let uu____3191 =
                                          FStar_Syntax_Print.term_to_string
                                            act_typ2
                                           in
                                        FStar_Util.print1
                                          "Action type after injecting it into the monad: %s\n"
                                          uu____3191
                                      else ());
                                     (let act2 =
                                        if
                                          act1.FStar_Syntax_Syntax.action_univs
                                            = []
                                        then
                                          let uu____3200 =
                                            FStar_TypeChecker_Util.generalize_universes
                                              env1 act_defn
                                             in
                                          match uu____3200 with
                                          | (us,act_defn1) ->
                                              let uu___446_3211 = act1  in
                                              let uu____3212 =
                                                FStar_Syntax_Subst.close_univ_vars
                                                  us act_typ2
                                                 in
                                              {
                                                FStar_Syntax_Syntax.action_name
                                                  =
                                                  (uu___446_3211.FStar_Syntax_Syntax.action_name);
                                                FStar_Syntax_Syntax.action_unqualified_name
                                                  =
                                                  (uu___446_3211.FStar_Syntax_Syntax.action_unqualified_name);
                                                FStar_Syntax_Syntax.action_univs
                                                  = us;
                                                FStar_Syntax_Syntax.action_params
                                                  =
                                                  (uu___446_3211.FStar_Syntax_Syntax.action_params);
                                                FStar_Syntax_Syntax.action_defn
                                                  = act_defn1;
                                                FStar_Syntax_Syntax.action_typ
                                                  = uu____3212
                                              }
                                        else
                                          (let uu___448_3215 = act1  in
                                           let uu____3216 =
                                             FStar_Syntax_Subst.close_univ_vars
                                               act1.FStar_Syntax_Syntax.action_univs
                                               act_defn
                                              in
                                           let uu____3217 =
                                             FStar_Syntax_Subst.close_univ_vars
                                               act1.FStar_Syntax_Syntax.action_univs
                                               act_typ2
                                              in
                                           {
                                             FStar_Syntax_Syntax.action_name
                                               =
                                               (uu___448_3215.FStar_Syntax_Syntax.action_name);
                                             FStar_Syntax_Syntax.action_unqualified_name
                                               =
                                               (uu___448_3215.FStar_Syntax_Syntax.action_unqualified_name);
                                             FStar_Syntax_Syntax.action_univs
                                               =
                                               (uu___448_3215.FStar_Syntax_Syntax.action_univs);
                                             FStar_Syntax_Syntax.action_params
                                               =
                                               (uu___448_3215.FStar_Syntax_Syntax.action_params);
                                             FStar_Syntax_Syntax.action_defn
                                               = uu____3216;
                                             FStar_Syntax_Syntax.action_typ =
                                               uu____3217
                                           })
                                         in
                                      act2)))))))))
              in
           let fst1 uu____3237 =
             match uu____3237 with | (a,uu____3253,uu____3254) -> a  in
           let snd1 uu____3286 =
             match uu____3286 with | (uu____3301,b,uu____3303) -> b  in
           let thd uu____3335 =
             match uu____3335 with | (uu____3350,uu____3351,c) -> c  in
           let uu___466_3365 = ed  in
           let uu____3366 =
             FStar_List.map (tc_action env0) ed.FStar_Syntax_Syntax.actions
              in
           {
             FStar_Syntax_Syntax.is_layered =
               (uu___466_3365.FStar_Syntax_Syntax.is_layered);
             FStar_Syntax_Syntax.cattributes =
               (uu___466_3365.FStar_Syntax_Syntax.cattributes);
             FStar_Syntax_Syntax.mname =
               (uu___466_3365.FStar_Syntax_Syntax.mname);
             FStar_Syntax_Syntax.univs =
               (uu___466_3365.FStar_Syntax_Syntax.univs);
             FStar_Syntax_Syntax.binders =
               (uu___466_3365.FStar_Syntax_Syntax.binders);
             FStar_Syntax_Syntax.signature =
               ((fst1 signature), (snd1 signature));
             FStar_Syntax_Syntax.ret_wp =
               ((fst1 return_repr), (thd return_repr));
             FStar_Syntax_Syntax.bind_wp =
               ((fst1 bind_repr), (thd bind_repr));
             FStar_Syntax_Syntax.stronger =
               (uu___466_3365.FStar_Syntax_Syntax.stronger);
             FStar_Syntax_Syntax.match_wps =
               (uu___466_3365.FStar_Syntax_Syntax.match_wps);
             FStar_Syntax_Syntax.trivial =
               (uu___466_3365.FStar_Syntax_Syntax.trivial);
             FStar_Syntax_Syntax.repr = ((fst1 repr), (snd1 repr));
             FStar_Syntax_Syntax.return_repr =
               ((fst1 return_repr), (snd1 return_repr));
             FStar_Syntax_Syntax.bind_repr =
               ((fst1 bind_repr), (snd1 bind_repr));
             FStar_Syntax_Syntax.stronger_repr =
               (uu___466_3365.FStar_Syntax_Syntax.stronger_repr);
             FStar_Syntax_Syntax.actions = uu____3366;
             FStar_Syntax_Syntax.eff_attrs =
               (uu___466_3365.FStar_Syntax_Syntax.eff_attrs)
           })))))
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      (let uu____3405 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "ED")
          in
       if uu____3405
       then
         let uu____3410 = FStar_Syntax_Print.eff_decl_to_string false ed  in
         FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____3410
       else ());
      (let uu____3416 =
         let uu____3421 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____3421 with
         | (ed_univs_subst,ed_univs) ->
             let bs =
               let uu____3445 =
                 FStar_Syntax_Subst.subst_binders ed_univs_subst
                   ed.FStar_Syntax_Syntax.binders
                  in
               FStar_Syntax_Subst.open_binders uu____3445  in
             let uu____3446 =
               let uu____3453 =
                 FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
               FStar_TypeChecker_TcTerm.tc_tparams uu____3453 bs  in
             (match uu____3446 with
              | (bs1,uu____3459,uu____3460) ->
                  let uu____3461 =
                    let tmp_t =
                      let uu____3471 =
                        let uu____3474 =
                          FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                            (fun _3479  -> FStar_Pervasives_Native.Some _3479)
                           in
                        FStar_Syntax_Syntax.mk_Total'
                          FStar_Syntax_Syntax.t_unit uu____3474
                         in
                      FStar_Syntax_Util.arrow bs1 uu____3471  in
                    let uu____3480 =
                      FStar_TypeChecker_Util.generalize_universes env0 tmp_t
                       in
                    match uu____3480 with
                    | (us,tmp_t1) ->
                        let uu____3497 =
                          let uu____3498 =
                            let uu____3499 =
                              FStar_All.pipe_right tmp_t1
                                FStar_Syntax_Util.arrow_formals
                               in
                            FStar_All.pipe_right uu____3499
                              FStar_Pervasives_Native.fst
                             in
                          FStar_All.pipe_right uu____3498
                            FStar_Syntax_Subst.close_binders
                           in
                        (us, uu____3497)
                     in
                  (match uu____3461 with
                   | (us,bs2) ->
                       (match ed_univs with
                        | [] -> (us, bs2)
                        | uu____3568 ->
                            let uu____3571 =
                              ((FStar_List.length ed_univs) =
                                 (FStar_List.length us))
                                &&
                                (FStar_List.forall2
                                   (fun u1  ->
                                      fun u2  ->
                                        let uu____3578 =
                                          FStar_Syntax_Syntax.order_univ_name
                                            u1 u2
                                           in
                                        uu____3578 = Prims.int_zero) ed_univs
                                   us)
                               in
                            if uu____3571
                            then (us, bs2)
                            else
                              (let uu____3589 =
                                 let uu____3595 =
                                   let uu____3597 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length ed_univs)
                                      in
                                   let uu____3599 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length us)
                                      in
                                   FStar_Util.format3
                                     "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                     uu____3597 uu____3599
                                    in
                                 (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                   uu____3595)
                                  in
                               let uu____3603 =
                                 FStar_Ident.range_of_lid
                                   ed.FStar_Syntax_Syntax.mname
                                  in
                               FStar_Errors.raise_error uu____3589 uu____3603))))
          in
       match uu____3416 with
       | (us,bs) ->
           let ed1 =
             let uu___495_3611 = ed  in
             {
               FStar_Syntax_Syntax.is_layered =
                 (uu___495_3611.FStar_Syntax_Syntax.is_layered);
               FStar_Syntax_Syntax.cattributes =
                 (uu___495_3611.FStar_Syntax_Syntax.cattributes);
               FStar_Syntax_Syntax.mname =
                 (uu___495_3611.FStar_Syntax_Syntax.mname);
               FStar_Syntax_Syntax.univs = us;
               FStar_Syntax_Syntax.binders = bs;
               FStar_Syntax_Syntax.signature =
                 (uu___495_3611.FStar_Syntax_Syntax.signature);
               FStar_Syntax_Syntax.ret_wp =
                 (uu___495_3611.FStar_Syntax_Syntax.ret_wp);
               FStar_Syntax_Syntax.bind_wp =
                 (uu___495_3611.FStar_Syntax_Syntax.bind_wp);
               FStar_Syntax_Syntax.stronger =
                 (uu___495_3611.FStar_Syntax_Syntax.stronger);
               FStar_Syntax_Syntax.match_wps =
                 (uu___495_3611.FStar_Syntax_Syntax.match_wps);
               FStar_Syntax_Syntax.trivial =
                 (uu___495_3611.FStar_Syntax_Syntax.trivial);
               FStar_Syntax_Syntax.repr =
                 (uu___495_3611.FStar_Syntax_Syntax.repr);
               FStar_Syntax_Syntax.return_repr =
                 (uu___495_3611.FStar_Syntax_Syntax.return_repr);
               FStar_Syntax_Syntax.bind_repr =
                 (uu___495_3611.FStar_Syntax_Syntax.bind_repr);
               FStar_Syntax_Syntax.stronger_repr =
                 (uu___495_3611.FStar_Syntax_Syntax.stronger_repr);
               FStar_Syntax_Syntax.actions =
                 (uu___495_3611.FStar_Syntax_Syntax.actions);
               FStar_Syntax_Syntax.eff_attrs =
                 (uu___495_3611.FStar_Syntax_Syntax.eff_attrs)
             }  in
           let uu____3612 = FStar_Syntax_Subst.univ_var_opening us  in
           (match uu____3612 with
            | (ed_univs_subst,ed_univs) ->
                let uu____3631 =
                  let uu____3636 =
                    FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                  FStar_Syntax_Subst.open_binders' uu____3636  in
                (match uu____3631 with
                 | (ed_bs,ed_bs_subst) ->
                     let ed2 =
                       let op uu____3657 =
                         match uu____3657 with
                         | (us1,t) ->
                             let t1 =
                               let uu____3677 =
                                 FStar_Syntax_Subst.shift_subst
                                   ((FStar_List.length ed_bs) +
                                      (FStar_List.length us1)) ed_univs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____3677 t  in
                             let uu____3686 =
                               let uu____3687 =
                                 FStar_Syntax_Subst.shift_subst
                                   (FStar_List.length us1) ed_bs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____3687 t1  in
                             (us1, uu____3686)
                          in
                       let uu___509_3692 = ed1  in
                       let uu____3693 = op ed1.FStar_Syntax_Syntax.signature
                          in
                       let uu____3694 = op ed1.FStar_Syntax_Syntax.ret_wp  in
                       let uu____3695 = op ed1.FStar_Syntax_Syntax.bind_wp
                          in
                       let uu____3696 = op ed1.FStar_Syntax_Syntax.stronger
                          in
                       let uu____3697 =
                         FStar_Syntax_Util.map_match_wps op
                           ed1.FStar_Syntax_Syntax.match_wps
                          in
                       let uu____3702 =
                         FStar_Util.map_opt ed1.FStar_Syntax_Syntax.trivial
                           op
                          in
                       let uu____3705 = op ed1.FStar_Syntax_Syntax.repr  in
                       let uu____3706 =
                         op ed1.FStar_Syntax_Syntax.return_repr  in
                       let uu____3707 = op ed1.FStar_Syntax_Syntax.bind_repr
                          in
                       let uu____3708 =
                         FStar_List.map
                           (fun a  ->
                              let uu___512_3716 = a  in
                              let uu____3717 =
                                let uu____3718 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_defn))
                                   in
                                FStar_Pervasives_Native.snd uu____3718  in
                              let uu____3729 =
                                let uu____3730 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_typ))
                                   in
                                FStar_Pervasives_Native.snd uu____3730  in
                              {
                                FStar_Syntax_Syntax.action_name =
                                  (uu___512_3716.FStar_Syntax_Syntax.action_name);
                                FStar_Syntax_Syntax.action_unqualified_name =
                                  (uu___512_3716.FStar_Syntax_Syntax.action_unqualified_name);
                                FStar_Syntax_Syntax.action_univs =
                                  (uu___512_3716.FStar_Syntax_Syntax.action_univs);
                                FStar_Syntax_Syntax.action_params =
                                  (uu___512_3716.FStar_Syntax_Syntax.action_params);
                                FStar_Syntax_Syntax.action_defn = uu____3717;
                                FStar_Syntax_Syntax.action_typ = uu____3729
                              }) ed1.FStar_Syntax_Syntax.actions
                          in
                       {
                         FStar_Syntax_Syntax.is_layered =
                           (uu___509_3692.FStar_Syntax_Syntax.is_layered);
                         FStar_Syntax_Syntax.cattributes =
                           (uu___509_3692.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.mname =
                           (uu___509_3692.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.univs =
                           (uu___509_3692.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___509_3692.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature = uu____3693;
                         FStar_Syntax_Syntax.ret_wp = uu____3694;
                         FStar_Syntax_Syntax.bind_wp = uu____3695;
                         FStar_Syntax_Syntax.stronger = uu____3696;
                         FStar_Syntax_Syntax.match_wps = uu____3697;
                         FStar_Syntax_Syntax.trivial = uu____3702;
                         FStar_Syntax_Syntax.repr = uu____3705;
                         FStar_Syntax_Syntax.return_repr = uu____3706;
                         FStar_Syntax_Syntax.bind_repr = uu____3707;
                         FStar_Syntax_Syntax.stronger_repr =
                           FStar_Pervasives_Native.None;
                         FStar_Syntax_Syntax.actions = uu____3708;
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___509_3692.FStar_Syntax_Syntax.eff_attrs)
                       }  in
                     ((let uu____3742 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env0)
                           (FStar_Options.Other "ED")
                          in
                       if uu____3742
                       then
                         let uu____3747 =
                           FStar_Syntax_Print.eff_decl_to_string false ed2
                            in
                         FStar_Util.print1
                           "After typechecking binders eff_decl: \n\t%s\n"
                           uu____3747
                       else ());
                      (let env =
                         let uu____3754 =
                           FStar_TypeChecker_Env.push_univ_vars env0 ed_univs
                            in
                         FStar_TypeChecker_Env.push_binders uu____3754 ed_bs
                          in
                       let check_and_gen' comb n1 env_opt uu____3789 k =
                         match uu____3789 with
                         | (us1,t) ->
                             let env1 =
                               if FStar_Util.is_some env_opt
                               then
                                 FStar_All.pipe_right env_opt FStar_Util.must
                               else env  in
                             let uu____3809 =
                               FStar_Syntax_Subst.open_univ_vars us1 t  in
                             (match uu____3809 with
                              | (us2,t1) ->
                                  let t2 =
                                    match k with
                                    | FStar_Pervasives_Native.Some k1 ->
                                        let uu____3818 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env1 us2
                                           in
                                        tc_check_trivial_guard uu____3818 t1
                                          k1
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____3819 =
                                          let uu____3826 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            uu____3826 t1
                                           in
                                        (match uu____3819 with
                                         | (t2,uu____3828,g) ->
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env1 g;
                                              t2))
                                     in
                                  let uu____3831 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env1 t2
                                     in
                                  (match uu____3831 with
                                   | (g_us,t3) ->
                                       (if (FStar_List.length g_us) <> n1
                                        then
                                          (let error =
                                             let uu____3847 =
                                               FStar_Util.string_of_int n1
                                                in
                                             let uu____3849 =
                                               let uu____3851 =
                                                 FStar_All.pipe_right g_us
                                                   FStar_List.length
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3851
                                                 FStar_Util.string_of_int
                                                in
                                             FStar_Util.format4
                                               "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                               (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                               comb uu____3847 uu____3849
                                              in
                                           FStar_Errors.raise_error
                                             (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                               error)
                                             t3.FStar_Syntax_Syntax.pos)
                                        else ();
                                        (match us2 with
                                         | [] -> (g_us, t3)
                                         | uu____3866 ->
                                             let uu____3867 =
                                               ((FStar_List.length us2) =
                                                  (FStar_List.length g_us))
                                                 &&
                                                 (FStar_List.forall2
                                                    (fun u1  ->
                                                       fun u2  ->
                                                         let uu____3874 =
                                                           FStar_Syntax_Syntax.order_univ_name
                                                             u1 u2
                                                            in
                                                         uu____3874 =
                                                           Prims.int_zero)
                                                    us2 g_us)
                                                in
                                             if uu____3867
                                             then (g_us, t3)
                                             else
                                               (let uu____3885 =
                                                  let uu____3891 =
                                                    let uu____3893 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           us2)
                                                       in
                                                    let uu____3895 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           g_us)
                                                       in
                                                    FStar_Util.format4
                                                      "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                      (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      comb uu____3893
                                                      uu____3895
                                                     in
                                                  (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                    uu____3891)
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____3885
                                                  t3.FStar_Syntax_Syntax.pos)))))
                          in
                       let signature =
                         check_and_gen' "signature" Prims.int_one
                           FStar_Pervasives_Native.None
                           ed2.FStar_Syntax_Syntax.signature
                           FStar_Pervasives_Native.None
                          in
                       (let uu____3903 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env0)
                            (FStar_Options.Other "ED")
                           in
                        if uu____3903
                        then
                          let uu____3908 =
                            FStar_Syntax_Print.tscheme_to_string signature
                             in
                          FStar_Util.print1 "Typechecked signature: %s\n"
                            uu____3908
                        else ());
                       (let fresh_a_and_wp uu____3924 =
                          let fail1 t =
                            let uu____3937 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env ed2.FStar_Syntax_Syntax.mname t
                               in
                            FStar_Errors.raise_error uu____3937
                              (FStar_Pervasives_Native.snd
                                 ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                             in
                          let uu____3953 =
                            FStar_TypeChecker_Env.inst_tscheme signature  in
                          match uu____3953 with
                          | (uu____3964,signature1) ->
                              let uu____3966 =
                                let uu____3967 =
                                  FStar_Syntax_Subst.compress signature1  in
                                uu____3967.FStar_Syntax_Syntax.n  in
                              (match uu____3966 with
                               | FStar_Syntax_Syntax.Tm_arrow
                                   (bs1,uu____3977) ->
                                   let bs2 =
                                     FStar_Syntax_Subst.open_binders bs1  in
                                   (match bs2 with
                                    | (a,uu____4006)::(wp,uu____4008)::[] ->
                                        (a, (wp.FStar_Syntax_Syntax.sort))
                                    | uu____4037 -> fail1 signature1)
                               | uu____4038 -> fail1 signature1)
                           in
                        let log_combinator s ts =
                          let uu____4052 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "ED")
                             in
                          if uu____4052
                          then
                            let uu____4057 =
                              FStar_Syntax_Print.tscheme_to_string ts  in
                            FStar_Util.print3 "Typechecked %s:%s = %s\n"
                              (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                              s uu____4057
                          else ()  in
                        let ret_wp =
                          let uu____4063 = fresh_a_and_wp ()  in
                          match uu____4063 with
                          | (a,wp_sort) ->
                              let k =
                                let uu____4079 =
                                  let uu____4088 =
                                    FStar_Syntax_Syntax.mk_binder a  in
                                  let uu____4095 =
                                    let uu____4104 =
                                      let uu____4111 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      FStar_Syntax_Syntax.null_binder
                                        uu____4111
                                       in
                                    [uu____4104]  in
                                  uu____4088 :: uu____4095  in
                                let uu____4130 =
                                  FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                FStar_Syntax_Util.arrow uu____4079 uu____4130
                                 in
                              check_and_gen' "ret_wp" Prims.int_one
                                FStar_Pervasives_Native.None
                                ed2.FStar_Syntax_Syntax.ret_wp
                                (FStar_Pervasives_Native.Some k)
                           in
                        log_combinator "ret_wp" ret_wp;
                        (let bind_wp =
                           let uu____4138 = fresh_a_and_wp ()  in
                           match uu____4138 with
                           | (a,wp_sort_a) ->
                               let uu____4151 = fresh_a_and_wp ()  in
                               (match uu____4151 with
                                | (b,wp_sort_b) ->
                                    let wp_sort_a_b =
                                      let uu____4167 =
                                        let uu____4176 =
                                          let uu____4183 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____4183
                                           in
                                        [uu____4176]  in
                                      let uu____4196 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____4167
                                        uu____4196
                                       in
                                    let k =
                                      let uu____4202 =
                                        let uu____4211 =
                                          FStar_Syntax_Syntax.null_binder
                                            FStar_Syntax_Syntax.t_range
                                           in
                                        let uu____4218 =
                                          let uu____4227 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4234 =
                                            let uu____4243 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____4250 =
                                              let uu____4259 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              let uu____4266 =
                                                let uu____4275 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a_b
                                                   in
                                                [uu____4275]  in
                                              uu____4259 :: uu____4266  in
                                            uu____4243 :: uu____4250  in
                                          uu____4227 :: uu____4234  in
                                        uu____4211 :: uu____4218  in
                                      let uu____4318 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____4202
                                        uu____4318
                                       in
                                    check_and_gen' "bind_wp"
                                      (Prims.of_int (2))
                                      FStar_Pervasives_Native.None
                                      ed2.FStar_Syntax_Syntax.bind_wp
                                      (FStar_Pervasives_Native.Some k))
                            in
                         log_combinator "bind_wp" bind_wp;
                         (let stronger =
                            let uu____4326 = fresh_a_and_wp ()  in
                            match uu____4326 with
                            | (a,wp_sort_a) ->
                                let uu____4339 = FStar_Syntax_Util.type_u ()
                                   in
                                (match uu____4339 with
                                 | (t,uu____4345) ->
                                     let k =
                                       let uu____4349 =
                                         let uu____4358 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____4365 =
                                           let uu____4374 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____4381 =
                                             let uu____4390 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____4390]  in
                                           uu____4374 :: uu____4381  in
                                         uu____4358 :: uu____4365  in
                                       let uu____4421 =
                                         FStar_Syntax_Syntax.mk_Total t  in
                                       FStar_Syntax_Util.arrow uu____4349
                                         uu____4421
                                        in
                                     check_and_gen' "stronger" Prims.int_one
                                       FStar_Pervasives_Native.None
                                       ed2.FStar_Syntax_Syntax.stronger
                                       (FStar_Pervasives_Native.Some k))
                             in
                          log_combinator "stronger" stronger;
                          (let match_wps =
                             let uu____4433 =
                               FStar_Syntax_Util.get_match_with_close_wps
                                 ed2.FStar_Syntax_Syntax.match_wps
                                in
                             match uu____4433 with
                             | (if_then_else1,ite_wp,close_wp) ->
                                 let if_then_else2 =
                                   let uu____4448 = fresh_a_and_wp ()  in
                                   match uu____4448 with
                                   | (a,wp_sort_a) ->
                                       let p =
                                         let uu____4462 =
                                           let uu____4465 =
                                             FStar_Ident.range_of_lid
                                               ed2.FStar_Syntax_Syntax.mname
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____4465
                                            in
                                         let uu____4466 =
                                           let uu____4467 =
                                             FStar_Syntax_Util.type_u ()  in
                                           FStar_All.pipe_right uu____4467
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____4462 uu____4466
                                          in
                                       let k =
                                         let uu____4479 =
                                           let uu____4488 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____4495 =
                                             let uu____4504 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 p
                                                in
                                             let uu____4511 =
                                               let uu____4520 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               let uu____4527 =
                                                 let uu____4536 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____4536]  in
                                               uu____4520 :: uu____4527  in
                                             uu____4504 :: uu____4511  in
                                           uu____4488 :: uu____4495  in
                                         let uu____4573 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a
                                            in
                                         FStar_Syntax_Util.arrow uu____4479
                                           uu____4573
                                          in
                                       check_and_gen' "if_then_else"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         if_then_else1
                                         (FStar_Pervasives_Native.Some k)
                                    in
                                 (log_combinator "if_then_else" if_then_else2;
                                  (let ite_wp1 =
                                     let uu____4581 = fresh_a_and_wp ()  in
                                     match uu____4581 with
                                     | (a,wp_sort_a) ->
                                         let k =
                                           let uu____4597 =
                                             let uu____4606 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____4613 =
                                               let uu____4622 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____4622]  in
                                             uu____4606 :: uu____4613  in
                                           let uu____4647 =
                                             FStar_Syntax_Syntax.mk_Total
                                               wp_sort_a
                                              in
                                           FStar_Syntax_Util.arrow uu____4597
                                             uu____4647
                                            in
                                         check_and_gen' "ite_wp"
                                           Prims.int_one
                                           FStar_Pervasives_Native.None
                                           ite_wp
                                           (FStar_Pervasives_Native.Some k)
                                      in
                                   log_combinator "ite_wp" ite_wp1;
                                   (let close_wp1 =
                                      let uu____4655 = fresh_a_and_wp ()  in
                                      match uu____4655 with
                                      | (a,wp_sort_a) ->
                                          let b =
                                            let uu____4669 =
                                              let uu____4672 =
                                                FStar_Ident.range_of_lid
                                                  ed2.FStar_Syntax_Syntax.mname
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____4672
                                               in
                                            let uu____4673 =
                                              let uu____4674 =
                                                FStar_Syntax_Util.type_u ()
                                                 in
                                              FStar_All.pipe_right uu____4674
                                                FStar_Pervasives_Native.fst
                                               in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____4669 uu____4673
                                             in
                                          let wp_sort_b_a =
                                            let uu____4686 =
                                              let uu____4695 =
                                                let uu____4702 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    b
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____4702
                                                 in
                                              [uu____4695]  in
                                            let uu____4715 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4686 uu____4715
                                             in
                                          let k =
                                            let uu____4721 =
                                              let uu____4730 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4737 =
                                                let uu____4746 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    b
                                                   in
                                                let uu____4753 =
                                                  let uu____4762 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_b_a
                                                     in
                                                  [uu____4762]  in
                                                uu____4746 :: uu____4753  in
                                              uu____4730 :: uu____4737  in
                                            let uu____4793 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4721 uu____4793
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
                             let uu____4803 = fresh_a_and_wp ()  in
                             match uu____4803 with
                             | (a,wp_sort_a) ->
                                 let uu____4818 = FStar_Syntax_Util.type_u ()
                                    in
                                 (match uu____4818 with
                                  | (t,uu____4826) ->
                                      let k =
                                        let uu____4830 =
                                          let uu____4839 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4846 =
                                            let uu____4855 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_sort_a
                                               in
                                            [uu____4855]  in
                                          uu____4839 :: uu____4846  in
                                        let uu____4880 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____4830
                                          uu____4880
                                         in
                                      let trivial =
                                        let uu____4884 =
                                          FStar_All.pipe_right
                                            ed2.FStar_Syntax_Syntax.trivial
                                            FStar_Util.must
                                           in
                                        check_and_gen' "trivial"
                                          Prims.int_one
                                          FStar_Pervasives_Native.None
                                          uu____4884
                                          (FStar_Pervasives_Native.Some k)
                                         in
                                      (log_combinator "trivial" trivial;
                                       FStar_Pervasives_Native.Some trivial))
                              in
                           let uu____4899 =
                             let uu____4910 =
                               let uu____4911 =
                                 FStar_Syntax_Subst.compress
                                   (FStar_Pervasives_Native.snd
                                      ed2.FStar_Syntax_Syntax.repr)
                                  in
                               uu____4911.FStar_Syntax_Syntax.n  in
                             match uu____4910 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____4930 ->
                                 let repr =
                                   let uu____4932 = fresh_a_and_wp ()  in
                                   match uu____4932 with
                                   | (a,wp_sort_a) ->
                                       let uu____4945 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____4945 with
                                        | (t,uu____4951) ->
                                            let k =
                                              let uu____4955 =
                                                let uu____4964 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____4971 =
                                                  let uu____4980 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a
                                                     in
                                                  [uu____4980]  in
                                                uu____4964 :: uu____4971  in
                                              let uu____5005 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____4955 uu____5005
                                               in
                                            check_and_gen' "repr"
                                              Prims.int_one
                                              FStar_Pervasives_Native.None
                                              ed2.FStar_Syntax_Syntax.repr
                                              (FStar_Pervasives_Native.Some k))
                                    in
                                 (log_combinator "repr" repr;
                                  (let mk_repr' t wp =
                                     let uu____5025 =
                                       FStar_TypeChecker_Env.inst_tscheme
                                         repr
                                        in
                                     match uu____5025 with
                                     | (uu____5032,repr1) ->
                                         let repr2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.EraseUniverses;
                                             FStar_TypeChecker_Env.AllowUnboundUniverses]
                                             env repr1
                                            in
                                         let uu____5035 =
                                           let uu____5042 =
                                             let uu____5043 =
                                               let uu____5060 =
                                                 let uu____5071 =
                                                   FStar_All.pipe_right t
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____5088 =
                                                   let uu____5099 =
                                                     FStar_All.pipe_right wp
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____5099]  in
                                                 uu____5071 :: uu____5088  in
                                               (repr2, uu____5060)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5043
                                              in
                                           FStar_Syntax_Syntax.mk uu____5042
                                            in
                                         uu____5035
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                      in
                                   let mk_repr a wp =
                                     let uu____5165 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     mk_repr' uu____5165 wp  in
                                   let destruct_repr t =
                                     let uu____5180 =
                                       let uu____5181 =
                                         FStar_Syntax_Subst.compress t  in
                                       uu____5181.FStar_Syntax_Syntax.n  in
                                     match uu____5180 with
                                     | FStar_Syntax_Syntax.Tm_app
                                         (uu____5192,(t1,uu____5194)::
                                          (wp,uu____5196)::[])
                                         -> (t1, wp)
                                     | uu____5255 ->
                                         failwith "Unexpected repr type"
                                      in
                                   let return_repr =
                                     let uu____5266 = fresh_a_and_wp ()  in
                                     match uu____5266 with
                                     | (a,uu____5274) ->
                                         let x_a =
                                           let uu____5280 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x_a"
                                             FStar_Pervasives_Native.None
                                             uu____5280
                                            in
                                         let res =
                                           let wp =
                                             let uu____5288 =
                                               let uu____5293 =
                                                 let uu____5294 =
                                                   FStar_TypeChecker_Env.inst_tscheme
                                                     ret_wp
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5294
                                                   FStar_Pervasives_Native.snd
                                                  in
                                               let uu____5303 =
                                                 let uu____5304 =
                                                   let uu____5313 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____5313
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____5322 =
                                                   let uu____5333 =
                                                     let uu____5342 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         x_a
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____5342
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____5333]  in
                                                 uu____5304 :: uu____5322  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____5293 uu____5303
                                                in
                                             uu____5288
                                               FStar_Pervasives_Native.None
                                               FStar_Range.dummyRange
                                              in
                                           mk_repr a wp  in
                                         let k =
                                           let uu____5378 =
                                             let uu____5387 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____5394 =
                                               let uu____5403 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   x_a
                                                  in
                                               [uu____5403]  in
                                             uu____5387 :: uu____5394  in
                                           let uu____5428 =
                                             FStar_Syntax_Syntax.mk_Total res
                                              in
                                           FStar_Syntax_Util.arrow uu____5378
                                             uu____5428
                                            in
                                         let uu____5431 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env k
                                            in
                                         (match uu____5431 with
                                          | (k1,uu____5439,uu____5440) ->
                                              let env1 =
                                                let uu____5444 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env
                                                    (FStar_Pervasives_Native.snd
                                                       ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____5444
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
                                        let uu____5455 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            FStar_Parser_Const.range_0
                                            FStar_Syntax_Syntax.delta_constant
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_All.pipe_right uu____5455
                                          FStar_Syntax_Syntax.fv_to_tm
                                         in
                                      let uu____5456 = fresh_a_and_wp ()  in
                                      match uu____5456 with
                                      | (a,wp_sort_a) ->
                                          let uu____5469 = fresh_a_and_wp ()
                                             in
                                          (match uu____5469 with
                                           | (b,wp_sort_b) ->
                                               let wp_sort_a_b =
                                                 let uu____5485 =
                                                   let uu____5494 =
                                                     let uu____5501 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____5501
                                                      in
                                                   [uu____5494]  in
                                                 let uu____5514 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     wp_sort_b
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____5485 uu____5514
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
                                                 let uu____5522 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     a
                                                    in
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "x_a"
                                                   FStar_Pervasives_Native.None
                                                   uu____5522
                                                  in
                                               let wp_g_x =
                                                 let uu____5527 =
                                                   let uu____5532 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       wp_g
                                                      in
                                                   let uu____5533 =
                                                     let uu____5534 =
                                                       let uu____5543 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x_a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____5543
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____5534]  in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     uu____5532 uu____5533
                                                    in
                                                 uu____5527
                                                   FStar_Pervasives_Native.None
                                                   FStar_Range.dummyRange
                                                  in
                                               let res =
                                                 let wp =
                                                   let uu____5574 =
                                                     let uu____5579 =
                                                       let uu____5580 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           bind_wp
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____5580
                                                         FStar_Pervasives_Native.snd
                                                        in
                                                     let uu____5589 =
                                                       let uu____5590 =
                                                         let uu____5593 =
                                                           let uu____5596 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               a
                                                              in
                                                           let uu____5597 =
                                                             let uu____5600 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 b
                                                                in
                                                             let uu____5601 =
                                                               let uu____5604
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_f
                                                                  in
                                                               let uu____5605
                                                                 =
                                                                 let uu____5608
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g
                                                                    in
                                                                 [uu____5608]
                                                                  in
                                                               uu____5604 ::
                                                                 uu____5605
                                                                in
                                                             uu____5600 ::
                                                               uu____5601
                                                              in
                                                           uu____5596 ::
                                                             uu____5597
                                                            in
                                                         r :: uu____5593  in
                                                       FStar_List.map
                                                         FStar_Syntax_Syntax.as_arg
                                                         uu____5590
                                                        in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____5579 uu____5589
                                                      in
                                                   uu____5574
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 mk_repr b wp  in
                                               let maybe_range_arg =
                                                 let uu____5626 =
                                                   FStar_Util.for_some
                                                     (FStar_Syntax_Util.attr_eq
                                                        FStar_Syntax_Util.dm4f_bind_range_attr)
                                                     ed2.FStar_Syntax_Syntax.eff_attrs
                                                    in
                                                 if uu____5626
                                                 then
                                                   let uu____5637 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       FStar_Syntax_Syntax.t_range
                                                      in
                                                   let uu____5644 =
                                                     let uu____5653 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         FStar_Syntax_Syntax.t_range
                                                        in
                                                     [uu____5653]  in
                                                   uu____5637 :: uu____5644
                                                 else []  in
                                               let k =
                                                 let uu____5689 =
                                                   let uu____5698 =
                                                     let uu____5707 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____5714 =
                                                       let uu____5723 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           b
                                                          in
                                                       [uu____5723]  in
                                                     uu____5707 :: uu____5714
                                                      in
                                                   let uu____5748 =
                                                     let uu____5757 =
                                                       let uu____5766 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           wp_f
                                                          in
                                                       let uu____5773 =
                                                         let uu____5782 =
                                                           let uu____5789 =
                                                             let uu____5790 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp_f
                                                                in
                                                             mk_repr a
                                                               uu____5790
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____5789
                                                            in
                                                         let uu____5791 =
                                                           let uu____5800 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               wp_g
                                                              in
                                                           let uu____5807 =
                                                             let uu____5816 =
                                                               let uu____5823
                                                                 =
                                                                 let uu____5824
                                                                   =
                                                                   let uu____5833
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                   [uu____5833]
                                                                    in
                                                                 let uu____5852
                                                                   =
                                                                   let uu____5855
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                   FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____5855
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   uu____5824
                                                                   uu____5852
                                                                  in
                                                               FStar_Syntax_Syntax.null_binder
                                                                 uu____5823
                                                                in
                                                             [uu____5816]  in
                                                           uu____5800 ::
                                                             uu____5807
                                                            in
                                                         uu____5782 ::
                                                           uu____5791
                                                          in
                                                       uu____5766 ::
                                                         uu____5773
                                                        in
                                                     FStar_List.append
                                                       maybe_range_arg
                                                       uu____5757
                                                      in
                                                   FStar_List.append
                                                     uu____5698 uu____5748
                                                    in
                                                 let uu____5900 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     res
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____5689 uu____5900
                                                  in
                                               let uu____5903 =
                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                   env k
                                                  in
                                               (match uu____5903 with
                                                | (k1,uu____5911,uu____5912)
                                                    ->
                                                    let env1 =
                                                      FStar_TypeChecker_Env.set_range
                                                        env
                                                        (FStar_Pervasives_Native.snd
                                                           ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                       in
                                                    let env2 =
                                                      FStar_All.pipe_right
                                                        (let uu___710_5924 =
                                                           env1  in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.instantiate_imp);
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             = true;
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.nbe);
                                                           FStar_TypeChecker_Env.strict_args_tab
                                                             =
                                                             (uu___710_5924.FStar_TypeChecker_Env.strict_args_tab)
                                                         })
                                                        (fun _5926  ->
                                                           FStar_Pervasives_Native.Some
                                                             _5926)
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
                                         (let uu____5953 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env, act)
                                            else
                                              (let uu____5967 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____5967 with
                                               | (usubst,uvs) ->
                                                   let uu____5990 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env uvs
                                                      in
                                                   let uu____5991 =
                                                     let uu___723_5992 = act
                                                        in
                                                     let uu____5993 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____5994 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___723_5992.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___723_5992.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___723_5992.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____5993;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____5994
                                                     }  in
                                                   (uu____5990, uu____5991))
                                             in
                                          match uu____5953 with
                                          | (env1,act1) ->
                                              let act_typ =
                                                let uu____5998 =
                                                  let uu____5999 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  uu____5999.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____5998 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs1,c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c
                                                       in
                                                    let uu____6025 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname
                                                       in
                                                    if uu____6025
                                                    then
                                                      let uu____6028 =
                                                        let uu____6031 =
                                                          let uu____6032 =
                                                            let uu____6033 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____6033
                                                             in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____6032
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____6031
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____6028
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____6056 ->
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              let uu____6057 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env1 act_typ
                                                 in
                                              (match uu____6057 with
                                               | (act_typ1,uu____6065,g_t) ->
                                                   let env' =
                                                     let uu___740_6068 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env1 act_typ1
                                                        in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_sig
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.gamma_sig);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.attrtab
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.attrtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.phase1
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.phase1);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.uvar_subtyping
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.uvar_subtyping);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.fv_delta_depths
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.fv_delta_depths);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.postprocess
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.postprocess);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.nbe
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.nbe);
                                                       FStar_TypeChecker_Env.strict_args_tab
                                                         =
                                                         (uu___740_6068.FStar_TypeChecker_Env.strict_args_tab)
                                                     }  in
                                                   ((let uu____6071 =
                                                       FStar_TypeChecker_Env.debug
                                                         env1
                                                         (FStar_Options.Other
                                                            "ED")
                                                        in
                                                     if uu____6071
                                                     then
                                                       let uu____6075 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name
                                                          in
                                                       let uu____6077 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____6079 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1
                                                          in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____6075
                                                         uu____6077
                                                         uu____6079
                                                     else ());
                                                    (let uu____6084 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     match uu____6084 with
                                                     | (act_defn,uu____6092,g_a)
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
                                                         let uu____6096 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2
                                                              in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs1,c) ->
                                                               let uu____6132
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs1 c
                                                                  in
                                                               (match uu____6132
                                                                with
                                                                | (bs2,uu____6144)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____6151
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____6151
                                                                     in
                                                                    let uu____6154
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____6154
                                                                    with
                                                                    | 
                                                                    (k1,uu____6168,g)
                                                                    ->
                                                                    (k1, g)))
                                                           | uu____6172 ->
                                                               let uu____6173
                                                                 =
                                                                 let uu____6179
                                                                   =
                                                                   let uu____6181
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                   let uu____6183
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____6181
                                                                    uu____6183
                                                                    in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____6179)
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____6173
                                                                 act_defn1.FStar_Syntax_Syntax.pos
                                                            in
                                                         (match uu____6096
                                                          with
                                                          | (expected_k,g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env1
                                                                  act_typ2
                                                                  expected_k
                                                                 in
                                                              ((let uu____6201
                                                                  =
                                                                  let uu____6202
                                                                    =
                                                                    let uu____6203
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____6203
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____6202
                                                                   in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env1
                                                                  uu____6201);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____6205
                                                                    =
                                                                    let uu____6206
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____6206.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____6205
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____6231
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____6231
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____6238
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____6238
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____6258
                                                                    =
                                                                    let uu____6259
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____6259]
                                                                     in
                                                                    let uu____6260
                                                                    =
                                                                    let uu____6271
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____6271]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6258;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6260;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____6296
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____6296))
                                                                  | uu____6299
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                   in
                                                                let uu____6301
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
                                                                    let uu____6323
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____6323))
                                                                   in
                                                                match uu____6301
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
                                                                    let uu___790_6342
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___790_6342.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___790_6342.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___790_6342.FStar_Syntax_Syntax.action_params);
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
                           match uu____4899 with
                           | (repr,return_repr,bind_repr,actions) ->
                               let cl ts =
                                 let ts1 =
                                   FStar_Syntax_Subst.close_tscheme ed_bs ts
                                    in
                                 let ed_univs_closing =
                                   FStar_Syntax_Subst.univ_var_closing
                                     ed_univs
                                    in
                                 let uu____6367 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length ed_bs)
                                     ed_univs_closing
                                    in
                                 FStar_Syntax_Subst.subst_tscheme uu____6367
                                   ts1
                                  in
                               let ed3 =
                                 let uu___802_6377 = ed2  in
                                 let uu____6378 = cl signature  in
                                 let uu____6379 = cl ret_wp  in
                                 let uu____6380 = cl bind_wp  in
                                 let uu____6381 = cl stronger  in
                                 let uu____6382 =
                                   FStar_Syntax_Util.map_match_wps cl
                                     match_wps
                                    in
                                 let uu____6387 =
                                   FStar_Util.map_opt trivial cl  in
                                 let uu____6390 = cl repr  in
                                 let uu____6391 = cl return_repr  in
                                 let uu____6392 = cl bind_repr  in
                                 let uu____6393 =
                                   FStar_List.map
                                     (fun a  ->
                                        let uu___805_6401 = a  in
                                        let uu____6402 =
                                          let uu____6403 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_All.pipe_right uu____6403
                                            FStar_Pervasives_Native.snd
                                           in
                                        let uu____6428 =
                                          let uu____6429 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_All.pipe_right uu____6429
                                            FStar_Pervasives_Native.snd
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            (uu___805_6401.FStar_Syntax_Syntax.action_name);
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (uu___805_6401.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (uu___805_6401.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (uu___805_6401.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____6402;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____6428
                                        }) actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.is_layered =
                                     (uu___802_6377.FStar_Syntax_Syntax.is_layered);
                                   FStar_Syntax_Syntax.cattributes =
                                     (uu___802_6377.FStar_Syntax_Syntax.cattributes);
                                   FStar_Syntax_Syntax.mname =
                                     (uu___802_6377.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.univs =
                                     (uu___802_6377.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders =
                                     (uu___802_6377.FStar_Syntax_Syntax.binders);
                                   FStar_Syntax_Syntax.signature = uu____6378;
                                   FStar_Syntax_Syntax.ret_wp = uu____6379;
                                   FStar_Syntax_Syntax.bind_wp = uu____6380;
                                   FStar_Syntax_Syntax.stronger = uu____6381;
                                   FStar_Syntax_Syntax.match_wps = uu____6382;
                                   FStar_Syntax_Syntax.trivial = uu____6387;
                                   FStar_Syntax_Syntax.repr = uu____6390;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____6391;
                                   FStar_Syntax_Syntax.bind_repr = uu____6392;
                                   FStar_Syntax_Syntax.stronger_repr =
                                     FStar_Pervasives_Native.None;
                                   FStar_Syntax_Syntax.actions = uu____6393;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (uu___802_6377.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               ((let uu____6455 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____6455
                                 then
                                   let uu____6460 =
                                     FStar_Syntax_Print.eff_decl_to_string
                                       false ed3
                                      in
                                   FStar_Util.print1
                                     "Typechecked effect declaration:\n\t%s\n"
                                     uu____6460
                                 else ());
                                ed3))))))))))
  
let (cps_and_elaborate :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun ed  ->
      let uu____6487 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature)
         in
      match uu____6487 with
      | (effect_binders_un,signature_un) ->
          let uu____6508 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____6508 with
           | (effect_binders,env1,uu____6527) ->
               let uu____6528 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____6528 with
                | (signature,uu____6544) ->
                    let raise_error1 uu____6560 =
                      match uu____6560 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____6596  ->
                           match uu____6596 with
                           | (bv,qual) ->
                               let uu____6615 =
                                 let uu___830_6616 = bv  in
                                 let uu____6617 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___830_6616.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___830_6616.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____6617
                                 }  in
                               (uu____6615, qual)) effect_binders
                       in
                    let uu____6622 =
                      let uu____6629 =
                        let uu____6630 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____6630.FStar_Syntax_Syntax.n  in
                      match uu____6629 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____6640)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____6672 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____6622 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____6698 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____6698
                           then
                             let uu____6701 =
                               let uu____6704 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____6704  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____6701
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____6752 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____6752 with
                           | (t2,comp,uu____6765) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____6774 =
                           open_and_check env1 []
                             (FStar_Pervasives_Native.snd
                                ed.FStar_Syntax_Syntax.repr)
                            in
                         (match uu____6774 with
                          | (repr,_comp) ->
                              ((let uu____6802 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____6802
                                then
                                  let uu____6806 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____6806
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
                                let uu____6813 =
                                  recheck_debug "*" env1 wp_type  in
                                let wp_a =
                                  let uu____6816 =
                                    let uu____6817 =
                                      let uu____6818 =
                                        let uu____6835 =
                                          let uu____6846 =
                                            let uu____6855 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____6858 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____6855, uu____6858)  in
                                          [uu____6846]  in
                                        (wp_type, uu____6835)  in
                                      FStar_Syntax_Syntax.Tm_app uu____6818
                                       in
                                    mk1 uu____6817  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta] env1
                                    uu____6816
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____6906 =
                                      let uu____6913 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____6913)  in
                                    let uu____6919 =
                                      let uu____6928 =
                                        let uu____6935 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____6935
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____6928]  in
                                    uu____6906 :: uu____6919  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let uu____6972 =
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
                                  let uu____7038 = item  in
                                  match uu____7038 with
                                  | (u_item,item1) ->
                                      let uu____7053 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____7053 with
                                       | (item2,item_comp) ->
                                           ((let uu____7069 =
                                               let uu____7071 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____7071
                                                in
                                             if uu____7069
                                             then
                                               let uu____7074 =
                                                 let uu____7080 =
                                                   let uu____7082 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____7084 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____7082 uu____7084
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____7080)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____7074
                                             else ());
                                            (let uu____7090 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____7090 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let uu____7108 =
                                                   recheck_debug "*" env2
                                                     item_wp
                                                    in
                                                 let uu____7110 =
                                                   recheck_debug "_" env2
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab))))
                                   in
                                let uu____7112 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____7112 with
                                | (dmff_env1,uu____7138,bind_wp,bind_elab) ->
                                    let uu____7141 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____7141 with
                                     | (dmff_env2,uu____7167,return_wp,return_elab)
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
                                           let uu____7176 =
                                             let uu____7177 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____7177.FStar_Syntax_Syntax.n
                                              in
                                           match uu____7176 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____7235 =
                                                 let uu____7254 =
                                                   let uu____7259 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____7259
                                                    in
                                                 match uu____7254 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____7341 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____7235 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____7395 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____7395 [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____7418 =
                                                          let uu____7419 =
                                                            let uu____7436 =
                                                              let uu____7447
                                                                =
                                                                let uu____7456
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11)
                                                                   in
                                                                let uu____7461
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____7456,
                                                                  uu____7461)
                                                                 in
                                                              [uu____7447]
                                                               in
                                                            (wp_type,
                                                              uu____7436)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____7419
                                                           in
                                                        mk1 uu____7418  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Env.Beta]
                                                        env0 raw_wp_b1
                                                       in
                                                    let uu____7497 =
                                                      let uu____7506 =
                                                        let uu____7507 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____7507
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____7506
                                                       in
                                                    (match uu____7497 with
                                                     | (bs1,body2,what') ->
                                                         let fail1 uu____7530
                                                           =
                                                           let error_msg =
                                                             let uu____7533 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2
                                                                in
                                                             let uu____7535 =
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
                                                               uu____7533
                                                               uu____7535
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
                                                               ((let uu____7545
                                                                   =
                                                                   let uu____7547
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                   Prims.op_Negation
                                                                    uu____7547
                                                                    in
                                                                 if
                                                                   uu____7545
                                                                 then
                                                                   fail1 ()
                                                                 else ());
                                                                (let uu____7552
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
                                                                   uu____7552
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
                                                             let uu____7581 =
                                                               let uu____7586
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp
                                                                  in
                                                               let uu____7587
                                                                 =
                                                                 let uu____7588
                                                                   =
                                                                   let uu____7597
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                   (uu____7597,
                                                                    FStar_Pervasives_Native.None)
                                                                    in
                                                                 [uu____7588]
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____7586
                                                                 uu____7587
                                                                in
                                                             uu____7581
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange
                                                              in
                                                           let uu____7632 =
                                                             let uu____7633 =
                                                               let uu____7642
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp
                                                                  in
                                                               [uu____7642]
                                                                in
                                                             b11 ::
                                                               uu____7633
                                                              in
                                                           let uu____7667 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what
                                                              in
                                                           FStar_Syntax_Util.abs
                                                             uu____7632
                                                             uu____7667
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____7670 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let return_wp1 =
                                           let uu____7678 =
                                             let uu____7679 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____7679.FStar_Syntax_Syntax.n
                                              in
                                           match uu____7678 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____7737 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____7737
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____7758 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let bind_wp1 =
                                           let uu____7766 =
                                             let uu____7767 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____7767.FStar_Syntax_Syntax.n
                                              in
                                           match uu____7766 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_constant_at_level
                                                      Prims.int_one)
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let uu____7801 =
                                                 let uu____7802 =
                                                   let uu____7811 =
                                                     let uu____7818 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____7818
                                                      in
                                                   [uu____7811]  in
                                                 FStar_List.append uu____7802
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____7801 body what
                                           | uu____7837 ->
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
                                             (let uu____7867 =
                                                let uu____7868 =
                                                  let uu____7869 =
                                                    let uu____7886 =
                                                      let uu____7897 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____7897
                                                       in
                                                    (t, uu____7886)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____7869
                                                   in
                                                mk1 uu____7868  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____7867)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____7955 = f a2  in
                                               [uu____7955]
                                           | x::xs ->
                                               let uu____7966 =
                                                 apply_last1 f xs  in
                                               x :: uu____7966
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
                                           let uu____8000 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____8000 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____8030 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____8030
                                                 then
                                                   let uu____8033 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____8033
                                                 else ());
                                                (let uu____8038 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____8038))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____8047 =
                                                 let uu____8052 = mk_lid name
                                                    in
                                                 let uu____8053 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____8052 uu____8053
                                                  in
                                               (match uu____8047 with
                                                | (sigelt,fv) ->
                                                    ((let uu____8057 =
                                                        let uu____8060 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____8060
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____8057);
                                                     fv))
                                            in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp2 =
                                           register "return_wp" return_wp1
                                            in
                                         ((let uu____8114 =
                                             let uu____8117 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.PushOptions
                                                       (FStar_Pervasives_Native.Some
                                                          "--admit_smt_queries true")))
                                                in
                                             let uu____8120 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____8117 :: uu____8120  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____8114);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           (let uu____8172 =
                                              let uu____8175 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     FStar_Syntax_Syntax.PopOptions)
                                                 in
                                              let uu____8176 =
                                                FStar_ST.op_Bang sigelts  in
                                              uu____8175 :: uu____8176  in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____8172);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            (let uu____8228 =
                                               let uu____8231 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.PushOptions
                                                         (FStar_Pervasives_Native.Some
                                                            "--admit_smt_queries true")))
                                                  in
                                               let uu____8234 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____8231 :: uu____8234  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____8228);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             (let uu____8286 =
                                                let uu____8289 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       FStar_Syntax_Syntax.PopOptions)
                                                   in
                                                let uu____8290 =
                                                  FStar_ST.op_Bang sigelts
                                                   in
                                                uu____8289 :: uu____8290  in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____8286);
                                             (let uu____8339 =
                                                FStar_List.fold_left
                                                  (fun uu____8379  ->
                                                     fun action  ->
                                                       match uu____8379 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____8400 =
                                                             let uu____8407 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____8407
                                                               params_un
                                                              in
                                                           (match uu____8400
                                                            with
                                                            | (action_params,env',uu____8416)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____8442
                                                                     ->
                                                                    match uu____8442
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____8461
                                                                    =
                                                                    let uu___1023_8462
                                                                    = bv  in
                                                                    let uu____8463
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___1023_8462.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1023_8462.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____8463
                                                                    }  in
                                                                    (uu____8461,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____8469
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____8469
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
                                                                    uu____8508
                                                                    ->
                                                                    let uu____8509
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____8509
                                                                     in
                                                                    ((
                                                                    let uu____8513
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____8513
                                                                    then
                                                                    let uu____8518
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____8521
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____8524
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____8526
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____8518
                                                                    uu____8521
                                                                    uu____8524
                                                                    uu____8526
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
                                                                    let uu____8535
                                                                    =
                                                                    let uu____8538
                                                                    =
                                                                    let uu___1045_8539
                                                                    = action
                                                                     in
                                                                    let uu____8540
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____8541
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___1045_8539.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___1045_8539.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___1045_8539.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____8540;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____8541
                                                                    }  in
                                                                    uu____8538
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____8535))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____8339 with
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
                                                      let uu____8585 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____8592 =
                                                        let uu____8601 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____8601]  in
                                                      uu____8585 ::
                                                        uu____8592
                                                       in
                                                    let uu____8626 =
                                                      let uu____8629 =
                                                        let uu____8630 =
                                                          let uu____8631 =
                                                            let uu____8648 =
                                                              let uu____8659
                                                                =
                                                                let uu____8668
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____8671
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____8668,
                                                                  uu____8671)
                                                                 in
                                                              [uu____8659]
                                                               in
                                                            (repr,
                                                              uu____8648)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____8631
                                                           in
                                                        mk1 uu____8630  in
                                                      let uu____8707 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____8629
                                                        uu____8707
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____8626
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let uu____8708 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr2 =
                                                    register "repr" repr1  in
                                                  let uu____8712 =
                                                    let uu____8721 =
                                                      let uu____8722 =
                                                        let uu____8725 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____8725
                                                         in
                                                      uu____8722.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____8721 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____8739)
                                                        ->
                                                        let uu____8776 =
                                                          let uu____8797 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____8797
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____8865 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____8776
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____8930 =
                                                               let uu____8931
                                                                 =
                                                                 let uu____8934
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____8934
                                                                  in
                                                               uu____8931.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____8930
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____8967
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____8967
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____8982
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____9013
                                                                     ->
                                                                    match uu____9013
                                                                    with
                                                                    | 
                                                                    (bv,uu____9022)
                                                                    ->
                                                                    let uu____9027
                                                                    =
                                                                    let uu____9029
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____9029
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____9027
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____8982
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
                                                                    let uu____9121
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____9121
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____9131
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____9142
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____9142
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____9152
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____9155
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____9152,
                                                                    uu____9155)))
                                                              | uu____9170 ->
                                                                  let uu____9171
                                                                    =
                                                                    let uu____9177
                                                                    =
                                                                    let uu____9179
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____9179
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____9177)
                                                                     in
                                                                  raise_error1
                                                                    uu____9171))
                                                    | uu____9191 ->
                                                        let uu____9192 =
                                                          let uu____9198 =
                                                            let uu____9200 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type
                                                               in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____9200
                                                             in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____9198)
                                                           in
                                                        raise_error1
                                                          uu____9192
                                                     in
                                                  (match uu____8712 with
                                                   | (pre,post) ->
                                                       ((let uu____9233 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____9236 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____9239 =
                                                           register "wp"
                                                             wp_type
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___1101_9242
                                                             = ed  in
                                                           let uu____9243 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____9244 =
                                                             let uu____9245 =
                                                               FStar_Syntax_Subst.close
                                                                 effect_binders1
                                                                 effect_signature
                                                                in
                                                             ([], uu____9245)
                                                              in
                                                           let uu____9252 =
                                                             let uu____9253 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____9253)
                                                              in
                                                           let uu____9260 =
                                                             let uu____9261 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____9261)
                                                              in
                                                           let uu____9268 =
                                                             let uu____9269 =
                                                               apply_close
                                                                 repr2
                                                                in
                                                             ([], uu____9269)
                                                              in
                                                           let uu____9276 =
                                                             let uu____9277 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____9277)
                                                              in
                                                           let uu____9284 =
                                                             let uu____9285 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____9285)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.is_layered
                                                               =
                                                               (uu___1101_9242.FStar_Syntax_Syntax.is_layered);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___1101_9242.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___1101_9242.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___1101_9242.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____9243;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____9244;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____9252;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____9260;
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___1101_9242.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.match_wps
                                                               =
                                                               (uu___1101_9242.FStar_Syntax_Syntax.match_wps);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___1101_9242.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____9268;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____9276;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____9284;
                                                             FStar_Syntax_Syntax.stronger_repr
                                                               =
                                                               (uu___1101_9242.FStar_Syntax_Syntax.stronger_repr);
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___1101_9242.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____9292 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____9292
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____9310
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____9310
                                                               then
                                                                 let uu____9314
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____9314
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
                                                                    let uu____9334
                                                                    =
                                                                    let uu____9337
                                                                    =
                                                                    let uu____9338
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____9338)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____9337
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
                                                                    uu____9334;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____9345
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____9345
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____9348
                                                                 =
                                                                 let uu____9351
                                                                   =
                                                                   let uu____9354
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____9354
                                                                    in
                                                                 FStar_List.append
                                                                   uu____9351
                                                                   sigelts'
                                                                  in
                                                               (uu____9348,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____9395 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____9395 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____9430 = FStar_List.hd ses  in
            uu____9430.FStar_Syntax_Syntax.sigrng  in
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
           | uu____9435 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____9441,[],t,uu____9443,uu____9444);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____9446;
               FStar_Syntax_Syntax.sigattrs = uu____9447;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____9449,_t_top,_lex_t_top,_9483,uu____9452);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____9454;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____9455;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____9457,_t_cons,_lex_t_cons,_9491,uu____9460);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____9462;
                 FStar_Syntax_Syntax.sigattrs = uu____9463;_}::[]
               when
               ((_9483 = Prims.int_zero) && (_9491 = Prims.int_zero)) &&
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
                 let uu____9516 =
                   let uu____9523 =
                     let uu____9524 =
                       let uu____9531 =
                         let uu____9534 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____9534
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____9531, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____9524  in
                   FStar_Syntax_Syntax.mk uu____9523  in
                 uu____9516 FStar_Pervasives_Native.None r1  in
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
                   let uu____9549 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____9549
                    in
                 let hd1 =
                   let uu____9551 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____9551
                    in
                 let tl1 =
                   let uu____9553 =
                     let uu____9554 =
                       let uu____9561 =
                         let uu____9562 =
                           let uu____9569 =
                             let uu____9572 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____9572
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____9569, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____9562  in
                       FStar_Syntax_Syntax.mk uu____9561  in
                     uu____9554 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____9553
                    in
                 let res =
                   let uu____9578 =
                     let uu____9585 =
                       let uu____9586 =
                         let uu____9593 =
                           let uu____9596 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____9596
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____9593,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____9586  in
                     FStar_Syntax_Syntax.mk uu____9585  in
                   uu____9578 FStar_Pervasives_Native.None r2  in
                 let uu____9599 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____9599
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
               let uu____9638 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____9638;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____9643 ->
               let err_msg =
                 let uu____9648 =
                   let uu____9650 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____9650  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____9648
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
    fun uu____9675  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____9675 with
          | (uvs,t) ->
              let uu____9688 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____9688 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____9700 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____9700 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____9718 =
                        let uu____9721 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____9721
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____9718)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____9744 =
          let uu____9745 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____9745 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____9744 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____9770 =
          let uu____9771 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____9771 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____9770 r
  
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
          (let uu____9820 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____9820
           then
             let uu____9823 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____9823
           else ());
          (let uu____9828 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____9828 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____9859 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____9859 FStar_List.flatten  in
               ((let uu____9873 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____9876 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____9876)
                    in
                 if uu____9873
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
                           let uu____9892 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____9902,uu____9903,uu____9904,uu____9905,uu____9906)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____9915 -> failwith "Impossible!"  in
                           match uu____9892 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Inductive type "
                                      (Prims.op_Hat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____9934 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____9944,uu____9945,ty_lid,uu____9947,uu____9948)
                               -> (data_lid, ty_lid)
                           | uu____9955 -> failwith "Impossible"  in
                         match uu____9934 with
                         | (data_lid,ty_lid) ->
                             let uu____9963 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____9966 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____9966)
                                in
                             if uu____9963
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Exception "
                                      (Prims.op_Hat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____9980 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____9985,uu____9986,uu____9987,uu____9988,uu____9989)
                         -> lid
                     | uu____9998 -> failwith "Impossible"  in
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
                   let uu____10016 =
                     (((FStar_List.length tcs) = Prims.int_zero) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____10016
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
          let pop1 uu____10091 =
            let uu____10092 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___1279_10102  ->
               match () with
               | () ->
                   let uu____10109 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____10109 (fun r  -> pop1 (); r))
              ()
          with
          | uu___1278_10140 -> (pop1 (); FStar_Exn.raise uu___1278_10140)
  
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
      | uu____10456 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____10514 = FStar_ToSyntax_ToSyntax.get_fail_attr true at
              in
           comb uu____10514 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____10539 .
    'Auu____10539 FStar_Pervasives_Native.option -> 'Auu____10539 Prims.list
  =
  fun uu___0_10548  ->
    match uu___0_10548 with
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
            let uu____10628 = collect1 tl1  in
            (match uu____10628 with
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
        | ((e,n1)::uu____10866,[]) ->
            FStar_Pervasives_Native.Some (e, n1, Prims.int_zero)
        | ([],(e,n1)::uu____10922) ->
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
          let uu____11132 =
            let uu____11134 = FStar_Options.ide ()  in
            Prims.op_Negation uu____11134  in
          if uu____11132
          then
            let uu____11137 =
              let uu____11142 = FStar_TypeChecker_Env.dsenv env  in
              let uu____11143 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____11142 uu____11143  in
            (match uu____11137 with
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
                              let uu____11176 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____11177 =
                                let uu____11183 =
                                  let uu____11185 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____11187 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____11185 uu____11187
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____11183)
                                 in
                              FStar_Errors.log_issue uu____11176 uu____11177
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____11194 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____11195 =
                                   let uu____11201 =
                                     let uu____11203 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____11203
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____11201)
                                    in
                                 FStar_Errors.log_issue uu____11194
                                   uu____11195)
                              else ())
                         else ())))
          else ()
      | uu____11213 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____11258 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____11286 ->
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
             let uu____11346 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____11346
             then
               let ses1 =
                 let uu____11354 =
                   let uu____11355 =
                     let uu____11356 =
                       tc_inductive
                         (let uu___1411_11365 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1411_11365.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1411_11365.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1411_11365.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1411_11365.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1411_11365.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1411_11365.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1411_11365.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1411_11365.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1411_11365.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1411_11365.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1411_11365.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1411_11365.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1411_11365.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1411_11365.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1411_11365.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1411_11365.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1411_11365.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1411_11365.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1411_11365.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1411_11365.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1411_11365.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___1411_11365.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1411_11365.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1411_11365.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1411_11365.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1411_11365.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1411_11365.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1411_11365.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1411_11365.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1411_11365.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1411_11365.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1411_11365.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1411_11365.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1411_11365.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1411_11365.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1411_11365.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1411_11365.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1411_11365.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1411_11365.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1411_11365.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1411_11365.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1411_11365.FStar_TypeChecker_Env.strict_args_tab)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____11356
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____11355
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____11354
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____11379 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____11379
                 then
                   let uu____11384 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1415_11388 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1415_11388.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1415_11388.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1415_11388.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1415_11388.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____11384
                 else ());
                ses1)
             else ses  in
           let uu____11398 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____11398 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___1422_11422 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1422_11422.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1422_11422.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1422_11422.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1422_11422.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____11434 = cps_and_elaborate env ne  in
           (match uu____11434 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___1436_11473 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1436_11473.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1436_11473.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1436_11473.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1436_11473.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___1439_11475 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1439_11475.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1439_11475.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1439_11475.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1439_11475.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses), env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           ((let uu____11482 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "LayeredEffects")
                in
             if uu____11482
             then
               let uu____11487 = FStar_Syntax_Print.sigelt_to_string se  in
               FStar_Util.print1
                 "Starting to typecheck layered effect:\n%s\n" uu____11487
             else ());
            (let tc_fun =
               if ne.FStar_Syntax_Syntax.is_layered
               then tc_layered_eff_decl
               else tc_eff_decl  in
             let ne1 =
               let uu____11511 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env)
                  in
               if uu____11511
               then
                 let ne1 =
                   let uu____11515 =
                     let uu____11516 =
                       let uu____11517 =
                         tc_fun
                           (let uu___1449_11520 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1449_11520.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1449_11520.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1449_11520.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1449_11520.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1449_11520.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1449_11520.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1449_11520.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1449_11520.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1449_11520.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1449_11520.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1449_11520.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1449_11520.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1449_11520.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1449_11520.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1449_11520.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1449_11520.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1449_11520.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1449_11520.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1449_11520.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1449_11520.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1449_11520.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 = true;
                              FStar_TypeChecker_Env.failhard =
                                (uu___1449_11520.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1449_11520.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1449_11520.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1449_11520.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1449_11520.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1449_11520.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1449_11520.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1449_11520.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1449_11520.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1449_11520.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1449_11520.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1449_11520.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1449_11520.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1449_11520.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1449_11520.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1449_11520.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1449_11520.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1449_11520.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1449_11520.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1449_11520.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1449_11520.FStar_TypeChecker_Env.strict_args_tab)
                            }) ne
                          in
                       FStar_All.pipe_right uu____11517
                         (fun ne1  ->
                            let uu___1452_11526 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_new_effect ne1);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___1452_11526.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___1452_11526.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___1452_11526.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___1452_11526.FStar_Syntax_Syntax.sigattrs)
                            })
                        in
                     FStar_All.pipe_right uu____11516
                       (FStar_TypeChecker_Normalize.elim_uvars env)
                      in
                   FStar_All.pipe_right uu____11515
                     FStar_Syntax_Util.eff_decl_of_new_effect
                    in
                 ((let uu____11528 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "TwoPhases")
                      in
                   if uu____11528
                   then
                     let uu____11533 =
                       FStar_Syntax_Print.sigelt_to_string
                         (let uu___1456_11537 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1456_11537.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1456_11537.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1456_11537.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1456_11537.FStar_Syntax_Syntax.sigattrs)
                          })
                        in
                     FStar_Util.print1 "Effect decl after phase 1: %s\n"
                       uu____11533
                   else ());
                  ne1)
               else ne  in
             let ne2 = tc_fun env ne1  in
             let se1 =
               let uu___1461_11545 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_new_effect ne2);
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1461_11545.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1461_11545.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1461_11545.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1461_11545.FStar_Syntax_Syntax.sigattrs)
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
           let uu____11553 =
             let uu____11560 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____11560
              in
           (match uu____11553 with
            | (a,wp_a_src) ->
                let uu____11577 =
                  let uu____11584 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____11584
                   in
                (match uu____11577 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____11602 =
                         let uu____11605 =
                           let uu____11606 =
                             let uu____11613 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____11613)  in
                           FStar_Syntax_Syntax.NT uu____11606  in
                         [uu____11605]  in
                       FStar_Syntax_Subst.subst uu____11602 wp_b_tgt  in
                     let expected_k =
                       let uu____11621 =
                         let uu____11630 = FStar_Syntax_Syntax.mk_binder a
                            in
                         let uu____11637 =
                           let uu____11646 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____11646]  in
                         uu____11630 :: uu____11637  in
                       let uu____11671 =
                         FStar_Syntax_Syntax.mk_Total wp_a_tgt  in
                       FStar_Syntax_Util.arrow uu____11621 uu____11671  in
                     let repr_type eff_name a1 wp =
                       (let uu____11693 =
                          let uu____11695 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name
                             in
                          Prims.op_Negation uu____11695  in
                        if uu____11693
                        then
                          let uu____11698 =
                            let uu____11704 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____11704)
                             in
                          let uu____11708 =
                            FStar_TypeChecker_Env.get_range env  in
                          FStar_Errors.raise_error uu____11698 uu____11708
                        else ());
                       (let uu____11711 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name
                           in
                        match uu____11711 with
                        | FStar_Pervasives_Native.None  ->
                            failwith
                              "internal error: reifiable effect has no decl?"
                        | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                            let repr =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [FStar_Syntax_Syntax.U_unknown] env ed
                                ed.FStar_Syntax_Syntax.repr
                               in
                            let uu____11744 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____11745 =
                              let uu____11752 =
                                let uu____11753 =
                                  let uu____11770 =
                                    let uu____11781 =
                                      FStar_Syntax_Syntax.as_arg a1  in
                                    let uu____11790 =
                                      let uu____11801 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____11801]  in
                                    uu____11781 :: uu____11790  in
                                  (repr, uu____11770)  in
                                FStar_Syntax_Syntax.Tm_app uu____11753  in
                              FStar_Syntax_Syntax.mk uu____11752  in
                            uu____11745 FStar_Pervasives_Native.None
                              uu____11744)
                        in
                     let uu____11846 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____12019 =
                             if (FStar_List.length uvs) > Prims.int_zero
                             then
                               let uu____12030 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____12030 with
                               | (usubst,uvs1) ->
                                   let uu____12053 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____12054 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____12053, uu____12054)
                             else (env, lift_wp)  in
                           (match uu____12019 with
                            | (env1,lift_wp1) ->
                                let lift_wp2 =
                                  if (FStar_List.length uvs) = Prims.int_zero
                                  then check_and_gen env1 lift_wp1 expected_k
                                  else
                                    (let lift_wp2 =
                                       tc_check_trivial_guard env1 lift_wp1
                                         expected_k
                                        in
                                     let uu____12104 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____12104))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____12175 =
                             if (FStar_List.length what) > Prims.int_zero
                             then
                               let uu____12190 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____12190 with
                               | (usubst,uvs) ->
                                   let uu____12215 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____12215)
                             else ([], lift)  in
                           (match uu____12175 with
                            | (uvs,lift1) ->
                                ((let uu____12251 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____12251
                                  then
                                    let uu____12255 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____12255
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____12261 =
                                    let uu____12268 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____12268 lift1
                                     in
                                  match uu____12261 with
                                  | (lift2,comp,uu____12293) ->
                                      let uu____12294 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____12294 with
                                       | (uu____12323,lift_wp,lift_elab) ->
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
                                             let uu____12355 =
                                               let uu____12366 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____12366
                                                in
                                             let uu____12383 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____12355, uu____12383)
                                           else
                                             (let uu____12412 =
                                                let uu____12423 =
                                                  let uu____12432 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____12432)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____12423
                                                 in
                                              let uu____12447 =
                                                let uu____12456 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____12456)  in
                                              (uu____12412, uu____12447))))))
                        in
                     (match uu____11846 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___1537_12530 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1537_12530.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1537_12530.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1537_12530.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1537_12530.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1537_12530.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1537_12530.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1537_12530.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1537_12530.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1537_12530.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1537_12530.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1537_12530.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1537_12530.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1537_12530.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1537_12530.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1537_12530.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1537_12530.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1537_12530.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1537_12530.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1537_12530.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1537_12530.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1537_12530.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1537_12530.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1537_12530.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1537_12530.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1537_12530.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1537_12530.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1537_12530.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1537_12530.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1537_12530.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1537_12530.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1537_12530.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1537_12530.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1537_12530.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1537_12530.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1537_12530.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1537_12530.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1537_12530.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1537_12530.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1537_12530.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1537_12530.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1537_12530.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1537_12530.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1537_12530.FStar_TypeChecker_Env.strict_args_tab)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____12587 =
                                  let uu____12592 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____12592 with
                                  | (usubst,uvs1) ->
                                      let uu____12615 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____12616 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____12615, uu____12616)
                                   in
                                (match uu____12587 with
                                 | (env2,lift2) ->
                                     let uu____12629 =
                                       let uu____12636 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____12636
                                        in
                                     (match uu____12629 with
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
                                              let uu____12670 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____12671 =
                                                let uu____12678 =
                                                  let uu____12679 =
                                                    let uu____12696 =
                                                      let uu____12707 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____12716 =
                                                        let uu____12727 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____12727]  in
                                                      uu____12707 ::
                                                        uu____12716
                                                       in
                                                    (lift_wp1, uu____12696)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____12679
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____12678
                                                 in
                                              uu____12671
                                                FStar_Pervasives_Native.None
                                                uu____12670
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____12775 =
                                              let uu____12784 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____12791 =
                                                let uu____12800 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____12807 =
                                                  let uu____12816 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____12816]  in
                                                uu____12800 :: uu____12807
                                                 in
                                              uu____12784 :: uu____12791  in
                                            let uu____12847 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____12775 uu____12847
                                             in
                                          let uu____12850 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____12850 with
                                           | (expected_k2,uu____12868,uu____12869)
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
                                                    let uu____12893 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____12893))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____12909 =
                              let uu____12911 =
                                let uu____12913 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____12913
                                  FStar_List.length
                                 in
                              uu____12911 <> Prims.int_one  in
                            if uu____12909
                            then
                              let uu____12935 =
                                let uu____12941 =
                                  let uu____12943 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____12945 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____12947 =
                                    let uu____12949 =
                                      let uu____12951 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____12951
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____12949
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____12943 uu____12945 uu____12947
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____12941)
                                 in
                              FStar_Errors.raise_error uu____12935 r
                            else ());
                           (let uu____12978 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____12989 =
                                   let uu____12991 =
                                     let uu____12994 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____12994
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____12991
                                     FStar_List.length
                                    in
                                 uu____12989 <> Prims.int_one)
                               in
                            if uu____12978
                            then
                              let uu____13048 =
                                let uu____13054 =
                                  let uu____13056 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____13058 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____13060 =
                                    let uu____13062 =
                                      let uu____13064 =
                                        let uu____13067 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____13067
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____13064
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____13062
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____13056 uu____13058 uu____13060
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____13054)
                                 in
                              FStar_Errors.raise_error uu____13048 r
                            else ());
                           (let sub2 =
                              let uu___1574_13126 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___1574_13126.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___1574_13126.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___1577_13128 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___1577_13128.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___1577_13128.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___1577_13128.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___1577_13128.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let uu____13142 =
             if (FStar_List.length uvs) = Prims.int_zero
             then (env, uvs, tps, c)
             else
               (let uu____13170 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____13170 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____13201 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____13201 c  in
                    let uu____13210 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____13210, uvs1, tps1, c1))
              in
           (match uu____13142 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____13232 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____13232 with
                 | (tps2,c2) ->
                     let uu____13249 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____13249 with
                      | (tps3,env3,us) ->
                          let uu____13269 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____13269 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____13297)::uu____13298 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____13317 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____13325 =
                                   let uu____13327 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____13327  in
                                 if uu____13325
                                 then
                                   let uu____13330 =
                                     let uu____13336 =
                                       let uu____13338 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____13340 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____13338 uu____13340
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____13336)
                                      in
                                   FStar_Errors.raise_error uu____13330 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____13348 =
                                   let uu____13349 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____13349
                                    in
                                 match uu____13348 with
                                 | (uvs2,t) ->
                                     let uu____13380 =
                                       let uu____13385 =
                                         let uu____13398 =
                                           let uu____13399 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____13399.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____13398)  in
                                       match uu____13385 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____13414,c5)) -> ([], c5)
                                       | (uu____13456,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____13495 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____13380 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               Prims.int_one
                                           then
                                             (let uu____13529 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____13529 with
                                              | (uu____13534,t1) ->
                                                  let uu____13536 =
                                                    let uu____13542 =
                                                      let uu____13544 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____13546 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____13550 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____13544
                                                        uu____13546
                                                        uu____13550
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____13542)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____13536 r)
                                           else ();
                                           (let se1 =
                                              let uu___1647_13557 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___1647_13557.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___1647_13557.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___1647_13557.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___1647_13557.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____13564,uu____13565,uu____13566) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_13571  ->
                   match uu___1_13571 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13574 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____13580,uu____13581) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_13590  ->
                   match uu___1_13590 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13593 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____13604 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____13604
             then
               let uu____13607 =
                 let uu____13613 =
                   let uu____13615 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____13615
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____13613)
                  in
               FStar_Errors.raise_error uu____13607 r
             else ());
            (let uu____13621 =
               let uu____13630 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____13630
               then
                 let uu____13641 =
                   tc_declare_typ
                     (let uu___1671_13644 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1671_13644.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1671_13644.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1671_13644.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1671_13644.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1671_13644.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1671_13644.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1671_13644.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1671_13644.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1671_13644.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1671_13644.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1671_13644.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1671_13644.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1671_13644.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1671_13644.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1671_13644.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1671_13644.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1671_13644.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1671_13644.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1671_13644.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1671_13644.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1671_13644.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1671_13644.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1671_13644.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1671_13644.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1671_13644.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1671_13644.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1671_13644.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1671_13644.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1671_13644.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1671_13644.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1671_13644.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1671_13644.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1671_13644.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1671_13644.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1671_13644.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1671_13644.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1671_13644.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1671_13644.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1671_13644.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1671_13644.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___1671_13644.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___1671_13644.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1671_13644.FStar_TypeChecker_Env.strict_args_tab)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____13641 with
                 | (uvs1,t1) ->
                     ((let uu____13669 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____13669
                       then
                         let uu____13674 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____13676 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____13674 uu____13676
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____13621 with
             | (uvs1,t1) ->
                 let uu____13711 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____13711 with
                  | (uvs2,t2) ->
                      ([(let uu___1684_13741 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1684_13741.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1684_13741.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1684_13741.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1684_13741.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____13746 =
             let uu____13755 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____13755
             then
               let uu____13766 =
                 tc_assume
                   (let uu___1693_13769 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1693_13769.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1693_13769.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1693_13769.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1693_13769.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1693_13769.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1693_13769.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1693_13769.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1693_13769.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1693_13769.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1693_13769.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1693_13769.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1693_13769.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1693_13769.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1693_13769.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1693_13769.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1693_13769.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1693_13769.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1693_13769.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1693_13769.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1693_13769.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1693_13769.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___1693_13769.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1693_13769.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1693_13769.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1693_13769.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1693_13769.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1693_13769.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1693_13769.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1693_13769.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1693_13769.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1693_13769.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1693_13769.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1693_13769.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1693_13769.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1693_13769.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1693_13769.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1693_13769.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1693_13769.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1693_13769.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1693_13769.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1693_13769.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1693_13769.FStar_TypeChecker_Env.strict_args_tab)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____13766 with
               | (uvs1,t1) ->
                   ((let uu____13795 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____13795
                     then
                       let uu____13800 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____13802 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____13800
                         uu____13802
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____13746 with
            | (uvs1,t1) ->
                let uu____13837 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____13837 with
                 | (uvs2,t2) ->
                     ([(let uu___1706_13867 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1706_13867.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1706_13867.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1706_13867.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1706_13867.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____13871 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____13871 with
            | (e1,c,g1) ->
                let uu____13891 =
                  let uu____13898 =
                    let uu____13901 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____13901  in
                  let uu____13902 =
                    let uu____13907 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____13907)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____13898 uu____13902
                   in
                (match uu____13891 with
                 | (e2,uu____13919,g) ->
                     ((let uu____13922 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____13922);
                      (let se1 =
                         let uu___1721_13924 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1721_13924.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1721_13924.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1721_13924.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1721_13924.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____13936 = FStar_Options.debug_any ()  in
             if uu____13936
             then
               let uu____13939 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____13941 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____13939
                 uu____13941
             else ());
            (let uu____13946 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____13946 with
             | (t1,uu____13964,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____13978 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____13978 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____13981 =
                              let uu____13987 =
                                let uu____13989 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____13991 =
                                  let uu____13993 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____13993
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____13989 uu____13991
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____13987)
                               in
                            FStar_Errors.raise_error uu____13981 r
                        | uu____14005 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___1742_14010 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1742_14010.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1742_14010.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1742_14010.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1742_14010.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1742_14010.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1742_14010.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1742_14010.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1742_14010.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1742_14010.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1742_14010.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1742_14010.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1742_14010.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1742_14010.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1742_14010.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1742_14010.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1742_14010.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1742_14010.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1742_14010.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1742_14010.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1742_14010.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___1742_14010.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1742_14010.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1742_14010.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1742_14010.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1742_14010.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1742_14010.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1742_14010.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1742_14010.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1742_14010.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1742_14010.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1742_14010.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1742_14010.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1742_14010.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1742_14010.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1742_14010.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1742_14010.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1742_14010.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1742_14010.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1742_14010.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1742_14010.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1742_14010.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___1742_14010.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1742_14010.FStar_TypeChecker_Env.strict_args_tab)
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
                 let uu____14078 =
                   let uu____14080 =
                     let uu____14089 = drop_logic val_q  in
                     let uu____14092 = drop_logic q'  in
                     (uu____14089, uu____14092)  in
                   match uu____14080 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____14078
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____14119 =
                      let uu____14125 =
                        let uu____14127 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____14129 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____14131 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____14127 uu____14129 uu____14131
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____14125)
                       in
                    FStar_Errors.raise_error uu____14119 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____14168 =
                   let uu____14169 = FStar_Syntax_Subst.compress def  in
                   uu____14169.FStar_Syntax_Syntax.n  in
                 match uu____14168 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____14181,uu____14182) -> binders
                 | uu____14207 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____14219;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____14324) -> val_bs1
                     | (uu____14355,[]) -> val_bs1
                     | ((body_bv,uu____14387)::bt,(val_bv,aqual)::vt) ->
                         let uu____14444 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____14468) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___1811_14482 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___1813_14485 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___1813_14485.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___1811_14482.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1811_14482.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____14444
                      in
                   let uu____14492 =
                     let uu____14499 =
                       let uu____14500 =
                         let uu____14515 = rename_binders1 def_bs val_bs  in
                         (uu____14515, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____14500  in
                     FStar_Syntax_Syntax.mk uu____14499  in
                   uu____14492 FStar_Pervasives_Native.None r1
               | uu____14534 -> typ1  in
             let uu___1819_14535 = lb  in
             let uu____14536 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___1819_14535.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1819_14535.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____14536;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1819_14535.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___1819_14535.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1819_14535.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1819_14535.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____14539 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____14594  ->
                     fun lb  ->
                       match uu____14594 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____14640 =
                             let uu____14652 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____14652 with
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
                                   | uu____14732 ->
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
                                  (let uu____14779 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____14779, quals_opt1)))
                              in
                           (match uu____14640 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____14539 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____14883 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___2_14889  ->
                                match uu___2_14889 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____14894 -> false))
                         in
                      if uu____14883
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____14907 =
                    let uu____14914 =
                      let uu____14915 =
                        let uu____14929 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____14929)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____14915  in
                    FStar_Syntax_Syntax.mk uu____14914  in
                  uu____14907 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___1862_14948 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1862_14948.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1862_14948.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1862_14948.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1862_14948.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1862_14948.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1862_14948.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1862_14948.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1862_14948.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1862_14948.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1862_14948.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1862_14948.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1862_14948.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1862_14948.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1862_14948.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1862_14948.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1862_14948.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1862_14948.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1862_14948.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1862_14948.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1862_14948.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1862_14948.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1862_14948.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1862_14948.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1862_14948.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1862_14948.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1862_14948.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1862_14948.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1862_14948.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1862_14948.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1862_14948.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1862_14948.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1862_14948.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1862_14948.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1862_14948.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1862_14948.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1862_14948.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1862_14948.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1862_14948.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1862_14948.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1862_14948.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1862_14948.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___1862_14948.FStar_TypeChecker_Env.strict_args_tab)
                  }  in
                let e1 =
                  let uu____14951 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____14951
                  then
                    let drop_lbtyp e_lax =
                      let uu____14960 =
                        let uu____14961 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____14961.FStar_Syntax_Syntax.n  in
                      match uu____14960 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____14983 =
                              let uu____14984 = FStar_Syntax_Subst.compress e
                                 in
                              uu____14984.FStar_Syntax_Syntax.n  in
                            match uu____14983 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____14988,lb1::[]),uu____14990) ->
                                let uu____15006 =
                                  let uu____15007 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____15007.FStar_Syntax_Syntax.n  in
                                (match uu____15006 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____15012 -> false)
                            | uu____15014 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___1887_15018 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___1889_15033 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___1889_15033.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___1889_15033.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___1889_15033.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___1889_15033.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___1889_15033.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___1889_15033.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___1887_15018.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___1887_15018.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____15036 -> e_lax  in
                    let uu____15037 =
                      FStar_Util.record_time
                        (fun uu____15045  ->
                           let uu____15046 =
                             let uu____15047 =
                               let uu____15048 =
                                 FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                   (let uu___1893_15057 = env'  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___1893_15057.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___1893_15057.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___1893_15057.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___1893_15057.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___1893_15057.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___1893_15057.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___1893_15057.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___1893_15057.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___1893_15057.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___1893_15057.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___1893_15057.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___1893_15057.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___1893_15057.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___1893_15057.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___1893_15057.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___1893_15057.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___1893_15057.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___1893_15057.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___1893_15057.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___1893_15057.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___1893_15057.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___1893_15057.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___1893_15057.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___1893_15057.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___1893_15057.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___1893_15057.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___1893_15057.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___1893_15057.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___1893_15057.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___1893_15057.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___1893_15057.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___1893_15057.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___1893_15057.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___1893_15057.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___1893_15057.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___1893_15057.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___1893_15057.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___1893_15057.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___1893_15057.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___1893_15057.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___1893_15057.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___1893_15057.FStar_TypeChecker_Env.strict_args_tab)
                                    }) e
                                  in
                               FStar_All.pipe_right uu____15048
                                 (fun uu____15070  ->
                                    match uu____15070 with
                                    | (e1,uu____15078,uu____15079) -> e1)
                                in
                             FStar_All.pipe_right uu____15047
                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                  env')
                              in
                           FStar_All.pipe_right uu____15046 drop_lbtyp)
                       in
                    match uu____15037 with
                    | (e1,ms) ->
                        ((let uu____15085 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TwoPhases")
                             in
                          if uu____15085
                          then
                            let uu____15090 =
                              FStar_Syntax_Print.term_to_string e1  in
                            FStar_Util.print1
                              "Let binding after phase 1: %s\n" uu____15090
                          else ());
                         (let uu____15096 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TCDeclTime")
                             in
                          if uu____15096
                          then
                            let uu____15101 = FStar_Util.string_of_int ms  in
                            FStar_Util.print1
                              "Let binding elaborated (phase 1) in %s milliseconds\n"
                              uu____15101
                          else ());
                         e1)
                  else e  in
                let uu____15108 =
                  let uu____15117 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____15117 with
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
                (match uu____15108 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___1923_15222 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___1923_15222.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1923_15222.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1923_15222.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1923_15222.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___1930_15235 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1930_15235.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1930_15235.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___1930_15235.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___1930_15235.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1930_15235.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1930_15235.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____15236 =
                       FStar_Util.record_time
                         (fun uu____15255  ->
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              env' e1)
                        in
                     (match uu____15236 with
                      | (r1,ms) ->
                          ((let uu____15283 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TCDeclTime")
                               in
                            if uu____15283
                            then
                              let uu____15288 = FStar_Util.string_of_int ms
                                 in
                              FStar_Util.print1
                                "Let binding typechecked in phase 2 in %s milliseconds\n"
                                uu____15288
                            else ());
                           (let uu____15293 =
                              match r1 with
                              | ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                                   FStar_Syntax_Syntax.pos = uu____15318;
                                   FStar_Syntax_Syntax.vars = uu____15319;_},uu____15320,g)
                                  when FStar_TypeChecker_Env.is_trivial g ->
                                  let lbs2 =
                                    let uu____15350 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.snd lbs1)
                                        (FStar_List.map rename_parameters)
                                       in
                                    ((FStar_Pervasives_Native.fst lbs1),
                                      uu____15350)
                                     in
                                  let lbs3 =
                                    let uu____15374 =
                                      match post_tau with
                                      | FStar_Pervasives_Native.Some tau ->
                                          FStar_List.map (postprocess_lb tau)
                                            (FStar_Pervasives_Native.snd lbs2)
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.snd lbs2
                                       in
                                    ((FStar_Pervasives_Native.fst lbs2),
                                      uu____15374)
                                     in
                                  let quals1 =
                                    match e2.FStar_Syntax_Syntax.n with
                                    | FStar_Syntax_Syntax.Tm_meta
                                        (uu____15397,FStar_Syntax_Syntax.Meta_desugared
                                         (FStar_Syntax_Syntax.Masked_effect
                                         ))
                                        ->
                                        FStar_Syntax_Syntax.HasMaskedEffect
                                        :: quals
                                    | uu____15402 -> quals  in
                                  ((let uu___1960_15411 = se1  in
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_let
                                           (lbs3, lids));
                                      FStar_Syntax_Syntax.sigrng =
                                        (uu___1960_15411.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals = quals1;
                                      FStar_Syntax_Syntax.sigmeta =
                                        (uu___1960_15411.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (uu___1960_15411.FStar_Syntax_Syntax.sigattrs)
                                    }), lbs3)
                              | uu____15414 ->
                                  failwith
                                    "impossible (typechecking should preserve Tm_let)"
                               in
                            match uu____15293 with
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
                                 (let uu____15470 = log env1  in
                                  if uu____15470
                                  then
                                    let uu____15473 =
                                      let uu____15475 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.snd lbs1)
                                          (FStar_List.map
                                             (fun lb  ->
                                                let should_log =
                                                  let uu____15495 =
                                                    let uu____15504 =
                                                      let uu____15505 =
                                                        let uu____15508 =
                                                          FStar_Util.right
                                                            lb.FStar_Syntax_Syntax.lbname
                                                           in
                                                        uu____15508.FStar_Syntax_Syntax.fv_name
                                                         in
                                                      uu____15505.FStar_Syntax_Syntax.v
                                                       in
                                                    FStar_TypeChecker_Env.try_lookup_val_decl
                                                      env1 uu____15504
                                                     in
                                                  match uu____15495 with
                                                  | FStar_Pervasives_Native.None
                                                       -> true
                                                  | uu____15517 -> false  in
                                                if should_log
                                                then
                                                  let uu____15529 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  let uu____15531 =
                                                    FStar_Syntax_Print.term_to_string
                                                      lb.FStar_Syntax_Syntax.lbtyp
                                                     in
                                                  FStar_Util.format2
                                                    "let %s : %s" uu____15529
                                                    uu____15531
                                                else ""))
                                         in
                                      FStar_All.pipe_right uu____15475
                                        (FStar_String.concat "\n")
                                       in
                                    FStar_Util.print1 "%s\n" uu____15473
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
      (let uu____15583 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____15583
       then
         let uu____15586 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____15586
       else ());
      (let uu____15591 = get_fail_se se  in
       match uu____15591 with
       | FStar_Pervasives_Native.Some (uu____15612,false ) when
           let uu____15629 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____15629 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___1991_15655 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___1991_15655.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___1991_15655.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___1991_15655.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___1991_15655.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___1991_15655.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___1991_15655.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___1991_15655.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___1991_15655.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___1991_15655.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___1991_15655.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___1991_15655.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___1991_15655.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___1991_15655.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___1991_15655.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___1991_15655.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___1991_15655.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___1991_15655.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___1991_15655.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___1991_15655.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___1991_15655.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___1991_15655.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___1991_15655.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___1991_15655.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___1991_15655.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___1991_15655.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___1991_15655.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___1991_15655.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___1991_15655.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___1991_15655.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___1991_15655.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___1991_15655.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___1991_15655.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___1991_15655.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___1991_15655.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___1991_15655.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___1991_15655.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___1991_15655.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___1991_15655.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___1991_15655.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___1991_15655.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___1991_15655.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___1991_15655.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___1991_15655.FStar_TypeChecker_Env.strict_args_tab)
               }
             else env1  in
           ((let uu____15660 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____15660
             then
               let uu____15663 =
                 let uu____15665 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____15665
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____15663
             else ());
            (let uu____15679 =
               FStar_Errors.catch_errors
                 (fun uu____15709  ->
                    FStar_Options.with_saved_options
                      (fun uu____15721  -> tc_decl' env' se))
                in
             match uu____15679 with
             | (errs,uu____15733) ->
                 ((let uu____15763 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____15763
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____15798 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____15798  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____15810 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____15821 =
                            let uu____15831 = check_multi_eq errnos1 actual
                               in
                            match uu____15831 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- Prims.int_one), (~- Prims.int_one),
                                  (~- Prims.int_one))
                             in
                          (match uu____15821 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____15896 =
                                   let uu____15902 =
                                     let uu____15904 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____15907 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____15910 =
                                       FStar_Util.string_of_int e  in
                                     let uu____15912 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____15914 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____15904 uu____15907 uu____15910
                                       uu____15912 uu____15914
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____15902)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____15896)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____15941 .
    'Auu____15941 ->
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
               (fun uu___3_15984  ->
                  match uu___3_15984 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____15987 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____15998) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____16006 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____16016 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____16021 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____16037 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____16063 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16089) ->
            let uu____16098 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____16098
            then
              let for_export_bundle se1 uu____16135 =
                match uu____16135 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____16174,uu____16175) ->
                         let dec =
                           let uu___2067_16185 = se1  in
                           let uu____16186 =
                             let uu____16187 =
                               let uu____16194 =
                                 let uu____16195 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____16195  in
                               (l, us, uu____16194)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____16187
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____16186;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___2067_16185.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___2067_16185.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___2067_16185.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____16205,uu____16206,uu____16207) ->
                         let dec =
                           let uu___2078_16215 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___2078_16215.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___2078_16215.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___2078_16215.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____16220 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____16243,uu____16244,uu____16245) ->
            let uu____16246 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____16246 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____16270 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____16270
            then
              ([(let uu___2094_16289 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___2094_16289.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___2094_16289.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___2094_16289.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____16292 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_16298  ->
                         match uu___4_16298 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____16301 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____16307 ->
                             true
                         | uu____16309 -> false))
                  in
               if uu____16292 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____16330 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____16335 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____16340 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____16345 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____16350 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____16368) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____16382 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____16382
            then ([], hidden)
            else
              (let dec =
                 let uu____16403 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____16403;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____16414 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____16414
            then
              let uu____16425 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___2131_16439 = se  in
                        let uu____16440 =
                          let uu____16441 =
                            let uu____16448 =
                              let uu____16449 =
                                let uu____16452 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____16452.FStar_Syntax_Syntax.fv_name  in
                              uu____16449.FStar_Syntax_Syntax.v  in
                            (uu____16448, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____16441  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____16440;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___2131_16439.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___2131_16439.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___2131_16439.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____16425, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____16475 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____16475
       then
         let uu____16478 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____16478
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____16483 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____16501 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
           uu____16518) ->
           let env1 =
             let uu___2152_16523 = env  in
             let uu____16524 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2152_16523.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2152_16523.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2152_16523.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2152_16523.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2152_16523.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2152_16523.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2152_16523.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2152_16523.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2152_16523.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2152_16523.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___2152_16523.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2152_16523.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2152_16523.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2152_16523.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2152_16523.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2152_16523.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2152_16523.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___2152_16523.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___2152_16523.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2152_16523.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2152_16523.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2152_16523.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2152_16523.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2152_16523.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2152_16523.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2152_16523.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2152_16523.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2152_16523.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2152_16523.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2152_16523.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2152_16523.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2152_16523.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2152_16523.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2152_16523.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____16524;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2152_16523.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2152_16523.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2152_16523.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___2152_16523.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2152_16523.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2152_16523.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2152_16523.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2152_16523.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2152_16523.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
           let env1 =
             let uu___2152_16526 = env  in
             let uu____16527 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2152_16526.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2152_16526.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2152_16526.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2152_16526.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2152_16526.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2152_16526.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2152_16526.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2152_16526.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2152_16526.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2152_16526.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___2152_16526.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2152_16526.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2152_16526.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2152_16526.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2152_16526.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2152_16526.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2152_16526.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___2152_16526.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___2152_16526.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2152_16526.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2152_16526.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2152_16526.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2152_16526.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2152_16526.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2152_16526.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2152_16526.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2152_16526.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2152_16526.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2152_16526.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2152_16526.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2152_16526.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2152_16526.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2152_16526.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2152_16526.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____16527;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2152_16526.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2152_16526.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2152_16526.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___2152_16526.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2152_16526.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2152_16526.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2152_16526.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2152_16526.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2152_16526.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions
           uu____16528) ->
           let env1 =
             let uu___2152_16531 = env  in
             let uu____16532 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2152_16531.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2152_16531.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2152_16531.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2152_16531.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2152_16531.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2152_16531.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2152_16531.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2152_16531.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2152_16531.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2152_16531.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___2152_16531.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2152_16531.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2152_16531.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2152_16531.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2152_16531.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2152_16531.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2152_16531.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___2152_16531.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___2152_16531.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2152_16531.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2152_16531.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2152_16531.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2152_16531.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2152_16531.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2152_16531.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2152_16531.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2152_16531.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2152_16531.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2152_16531.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2152_16531.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2152_16531.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2152_16531.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2152_16531.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2152_16531.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____16532;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2152_16531.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2152_16531.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2152_16531.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___2152_16531.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2152_16531.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2152_16531.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2152_16531.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2152_16531.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2152_16531.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____16533) ->
           let env1 =
             let uu___2152_16538 = env  in
             let uu____16539 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2152_16538.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2152_16538.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2152_16538.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2152_16538.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2152_16538.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2152_16538.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2152_16538.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2152_16538.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2152_16538.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2152_16538.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___2152_16538.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2152_16538.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2152_16538.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2152_16538.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2152_16538.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2152_16538.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2152_16538.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___2152_16538.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___2152_16538.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2152_16538.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2152_16538.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2152_16538.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2152_16538.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2152_16538.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2152_16538.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2152_16538.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2152_16538.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2152_16538.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2152_16538.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2152_16538.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2152_16538.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2152_16538.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2152_16538.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2152_16538.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____16539;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2152_16538.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2152_16538.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2152_16538.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___2152_16538.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2152_16538.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2152_16538.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2152_16538.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2152_16538.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2152_16538.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver )
           ->
           ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
              ();
            env)
       | FStar_Syntax_Syntax.Sig_pragma uu____16541 -> env
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____16542 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____16552 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____16552) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____16553,uu____16554,uu____16555) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_16560  ->
                   match uu___5_16560 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____16563 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____16565,uu____16566) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_16575  ->
                   match uu___5_16575 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____16578 -> false))
           -> env
       | uu____16580 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____16649 se =
        match uu____16649 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____16702 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____16702
              then
                let uu____16705 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____16705
              else ());
             (let uu____16710 = tc_decl env1 se  in
              match uu____16710 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____16763 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____16763
                             then
                               let uu____16767 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____16767
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____16783 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____16783
                             then
                               let uu____16787 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____16787
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
                    (let uu____16804 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____16804
                     then
                       let uu____16809 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____16818 =
                                  let uu____16820 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____16820 "\n"  in
                                Prims.op_Hat s uu____16818) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____16809
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____16830 =
                       let uu____16839 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____16839
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____16881 se1 =
                            match uu____16881 with
                            | (exports1,hidden1) ->
                                let uu____16909 = for_export env3 hidden1 se1
                                   in
                                (match uu____16909 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____16830 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____17063 = acc  in
        match uu____17063 with
        | (uu____17098,uu____17099,env1,uu____17101) ->
            let uu____17114 =
              FStar_Util.record_time
                (fun uu____17161  -> process_one_decl acc se)
               in
            (match uu____17114 with
             | (r,ms_elapsed) ->
                 ((let uu____17227 =
                     ((FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TCDeclTime"))
                        ||
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.attr_eq
                              FStar_Syntax_Util.tcdecltime_attr)
                           se.FStar_Syntax_Syntax.sigattrs))
                       || (FStar_Options.timing ())
                      in
                   if uu____17227
                   then
                     let uu____17231 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____17233 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____17231 uu____17233
                   else ());
                  r))
         in
      let uu____17238 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____17238 with
      | (ses1,exports,env1,uu____17286) ->
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
          let uu___2249_17324 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2249_17324.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2249_17324.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2249_17324.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2249_17324.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2249_17324.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2249_17324.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2249_17324.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2249_17324.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2249_17324.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2249_17324.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___2249_17324.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___2249_17324.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___2249_17324.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2249_17324.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2249_17324.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___2249_17324.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2249_17324.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___2249_17324.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2249_17324.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___2249_17324.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___2249_17324.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___2249_17324.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2249_17324.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2249_17324.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2249_17324.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2249_17324.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2249_17324.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2249_17324.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2249_17324.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2249_17324.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2249_17324.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2249_17324.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2249_17324.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2249_17324.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___2249_17324.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2249_17324.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2249_17324.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2249_17324.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2249_17324.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2249_17324.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2249_17324.FStar_TypeChecker_Env.strict_args_tab)
          }  in
        let check_term lid univs1 t =
          let uu____17344 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____17344 with
          | (univs2,t1) ->
              ((let uu____17352 =
                  let uu____17354 =
                    let uu____17360 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____17360  in
                  FStar_All.pipe_left uu____17354
                    (FStar_Options.Other "Exports")
                   in
                if uu____17352
                then
                  let uu____17364 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____17366 =
                    let uu____17368 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____17368
                      (FStar_String.concat ", ")
                     in
                  let uu____17385 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____17364 uu____17366 uu____17385
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____17391 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____17391 (fun a2  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____17417 =
             let uu____17419 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____17421 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____17419 uu____17421
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____17417);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____17432) ->
              let uu____17441 =
                let uu____17443 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____17443  in
              if uu____17441
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____17457,uu____17458) ->
              let t =
                let uu____17470 =
                  let uu____17477 =
                    let uu____17478 =
                      let uu____17493 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____17493)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____17478  in
                  FStar_Syntax_Syntax.mk uu____17477  in
                uu____17470 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____17509,uu____17510,uu____17511) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____17521 =
                let uu____17523 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____17523  in
              if uu____17521 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____17531,lbs),uu____17533) ->
              let uu____17544 =
                let uu____17546 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____17546  in
              if uu____17544
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
              let uu____17569 =
                let uu____17571 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____17571  in
              if uu____17569
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____17592 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____17593 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____17600 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____17601 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____17602 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____17603 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____17610 -> ()  in
        let uu____17611 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____17611 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____17717) -> true
             | uu____17719 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____17749 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____17788 ->
                   let uu____17789 =
                     let uu____17796 =
                       let uu____17797 =
                         let uu____17812 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____17812)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____17797  in
                     FStar_Syntax_Syntax.mk uu____17796  in
                   uu____17789 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____17829,uu____17830) ->
            let s1 =
              let uu___2375_17840 = s  in
              let uu____17841 =
                let uu____17842 =
                  let uu____17849 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____17849)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____17842  in
              let uu____17850 =
                let uu____17853 =
                  let uu____17856 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____17856  in
                FStar_Syntax_Syntax.Assumption :: uu____17853  in
              {
                FStar_Syntax_Syntax.sigel = uu____17841;
                FStar_Syntax_Syntax.sigrng =
                  (uu___2375_17840.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____17850;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2375_17840.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___2375_17840.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____17859 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____17884 lbdef =
        match uu____17884 with
        | (uvs,t) ->
            let attrs =
              let uu____17895 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____17895
              then
                let uu____17900 =
                  let uu____17901 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____17901
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____17900 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___2388_17904 = s  in
            let uu____17905 =
              let uu____17908 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____17908  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___2388_17904.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____17905;
              FStar_Syntax_Syntax.sigmeta =
                (uu___2388_17904.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____17926 -> failwith "Impossible!"  in
        let c_opt =
          let uu____17933 = FStar_Syntax_Util.is_unit t  in
          if uu____17933
          then
            let uu____17940 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____17940
          else
            (let uu____17947 =
               let uu____17948 = FStar_Syntax_Subst.compress t  in
               uu____17948.FStar_Syntax_Syntax.n  in
             match uu____17947 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____17955,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____17979 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____17991 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____17991
            then false
            else
              (let uu____17998 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____17998
               then true
               else
                 (let uu____18005 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____18005))
         in
      let extract_sigelt s =
        (let uu____18017 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____18017
         then
           let uu____18020 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____18020
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____18027 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____18047 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____18066 ->
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
                             (lid,uu____18112,uu____18113,uu____18114,uu____18115,uu____18116)
                             ->
                             ((let uu____18126 =
                                 let uu____18129 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____18129  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____18126);
                              (let uu____18178 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____18178 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____18182,uu____18183,uu____18184,uu____18185,uu____18186)
                             ->
                             ((let uu____18194 =
                                 let uu____18197 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____18197  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____18194);
                              sigelts1)
                         | uu____18246 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____18255 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____18255
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____18265 =
                    let uu___2452_18266 = s  in
                    let uu____18267 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2452_18266.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2452_18266.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____18267;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2452_18266.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2452_18266.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____18265])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____18278 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____18278
             then []
             else
               (let uu____18285 = lbs  in
                match uu____18285 with
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
                        (fun uu____18347  ->
                           match uu____18347 with
                           | (uu____18355,t,uu____18357) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____18374  ->
                             match uu____18374 with
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
                           (fun uu____18401  ->
                              match uu____18401 with
                              | (uu____18409,t,uu____18411) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____18423,uu____18424) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____18432 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____18461 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____18461) uu____18432
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____18465 =
                    let uu___2494_18466 = s  in
                    let uu____18467 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2494_18466.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2494_18466.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____18467;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2494_18466.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2494_18466.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____18465]
                else [])
             else
               (let uu____18474 =
                  let uu___2496_18475 = s  in
                  let uu____18476 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___2496_18475.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___2496_18475.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____18476;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___2496_18475.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___2496_18475.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____18474])
         | FStar_Syntax_Syntax.Sig_new_effect uu____18479 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18480 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____18481 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18482 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____18495 -> [s])
         in
      let uu___2508_18496 = m  in
      let uu____18497 =
        let uu____18498 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____18498 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___2508_18496.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____18497;
        FStar_Syntax_Syntax.exports =
          (uu___2508_18496.FStar_Syntax_Syntax.exports);
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
        (fun uu____18549  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____18596  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____18611 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____18611
  
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
      (let uu____18700 = FStar_Options.debug_any ()  in
       if uu____18700
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
         let uu___2533_18716 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___2533_18716.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___2533_18716.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___2533_18716.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___2533_18716.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___2533_18716.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___2533_18716.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___2533_18716.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___2533_18716.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___2533_18716.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___2533_18716.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___2533_18716.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___2533_18716.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___2533_18716.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___2533_18716.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___2533_18716.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___2533_18716.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___2533_18716.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___2533_18716.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___2533_18716.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___2533_18716.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___2533_18716.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___2533_18716.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___2533_18716.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___2533_18716.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___2533_18716.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___2533_18716.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___2533_18716.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___2533_18716.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___2533_18716.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___2533_18716.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___2533_18716.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___2533_18716.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___2533_18716.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___2533_18716.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___2533_18716.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___2533_18716.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___2533_18716.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___2533_18716.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___2533_18716.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___2533_18716.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___2533_18716.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___2533_18716.FStar_TypeChecker_Env.strict_args_tab)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____18718 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____18718 with
       | (ses,exports,env3) ->
           ((let uu___2541_18751 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___2541_18751.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___2541_18751.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___2541_18751.FStar_Syntax_Syntax.is_interface)
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
        let uu____18780 = tc_decls env decls  in
        match uu____18780 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___2550_18811 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___2550_18811.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___2550_18811.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___2550_18811.FStar_Syntax_Syntax.is_interface)
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
        let uu____18872 = tc_partial_modul env01 m  in
        match uu____18872 with
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
                (let uu____18909 = FStar_Errors.get_err_count ()  in
                 uu____18909 = Prims.int_zero)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____18920 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____18920
                then
                  let uu____18924 =
                    let uu____18926 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____18926 then "" else " (in lax mode) "  in
                  let uu____18934 =
                    let uu____18936 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____18936
                    then
                      let uu____18940 =
                        let uu____18942 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.op_Hat uu____18942 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____18940
                    else ""  in
                  let uu____18949 =
                    let uu____18951 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____18951
                    then
                      let uu____18955 =
                        let uu____18957 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____18957 "\n"  in
                      Prims.op_Hat "\nto: " uu____18955
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____18924
                    uu____18934 uu____18949
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___2576_18971 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2576_18971.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2576_18971.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2576_18971.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2576_18971.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2576_18971.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2576_18971.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2576_18971.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2576_18971.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2576_18971.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2576_18971.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2576_18971.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2576_18971.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2576_18971.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2576_18971.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2576_18971.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2576_18971.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2576_18971.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2576_18971.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2576_18971.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2576_18971.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2576_18971.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2576_18971.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2576_18971.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2576_18971.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2576_18971.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2576_18971.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2576_18971.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2576_18971.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2576_18971.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2576_18971.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2576_18971.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___2576_18971.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2576_18971.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2576_18971.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2576_18971.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2576_18971.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2576_18971.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2576_18971.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2576_18971.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2576_18971.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2576_18971.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2576_18971.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2576_18971.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let en02 =
                    let uu___2579_18973 = en01  in
                    let uu____18974 =
                      let uu____18989 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____18989, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2579_18973.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2579_18973.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2579_18973.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2579_18973.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2579_18973.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2579_18973.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2579_18973.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2579_18973.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2579_18973.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2579_18973.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2579_18973.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2579_18973.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2579_18973.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2579_18973.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2579_18973.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2579_18973.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2579_18973.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2579_18973.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2579_18973.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2579_18973.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2579_18973.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2579_18973.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2579_18973.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2579_18973.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2579_18973.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2579_18973.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2579_18973.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2579_18973.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2579_18973.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2579_18973.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2579_18973.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____18974;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2579_18973.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2579_18973.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2579_18973.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2579_18973.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2579_18973.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2579_18973.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2579_18973.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2579_18973.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2579_18973.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___2579_18973.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2579_18973.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2579_18973.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let uu____19035 =
                    let uu____19037 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____19037  in
                  if uu____19035
                  then
                    ((let uu____19041 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____19041 (fun a3  -> ()));
                     en02)
                  else en02  in
                let uu____19045 = tc_modul en0 modul_iface true  in
                match uu____19045 with
                | (modul_iface1,env) ->
                    ((let uu___2588_19058 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___2588_19058.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___2588_19058.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___2588_19058.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___2590_19062 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___2590_19062.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___2590_19062.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___2590_19062.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____19065 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____19065 FStar_Util.smap_clear);
               (let uu____19101 =
                  ((let uu____19105 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____19105) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____19108 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____19108)
                   in
                if uu____19101 then check_exports env modul exports else ());
               (let uu____19114 =
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____19114 (fun a4  -> ()));
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
        let uu____19129 =
          let uu____19131 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____19131  in
        push_context env uu____19129  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____19152 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____19163 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____19163 with | (uu____19170,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____19195 = FStar_Options.debug_any ()  in
         if uu____19195
         then
           let uu____19198 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____19198
         else ());
        (let uu____19210 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____19210
         then
           let uu____19213 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____19213
         else ());
        (let env1 =
           let uu___2620_19219 = env  in
           let uu____19220 =
             let uu____19222 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____19222  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___2620_19219.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___2620_19219.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___2620_19219.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___2620_19219.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___2620_19219.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___2620_19219.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___2620_19219.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___2620_19219.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___2620_19219.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___2620_19219.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___2620_19219.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___2620_19219.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___2620_19219.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___2620_19219.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___2620_19219.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___2620_19219.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___2620_19219.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___2620_19219.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___2620_19219.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___2620_19219.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____19220;
             FStar_TypeChecker_Env.lax_universes =
               (uu___2620_19219.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___2620_19219.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___2620_19219.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___2620_19219.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___2620_19219.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___2620_19219.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___2620_19219.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___2620_19219.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___2620_19219.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___2620_19219.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___2620_19219.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___2620_19219.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___2620_19219.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___2620_19219.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___2620_19219.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___2620_19219.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___2620_19219.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___2620_19219.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___2620_19219.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___2620_19219.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___2620_19219.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___2620_19219.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___2620_19219.FStar_TypeChecker_Env.strict_args_tab)
           }  in
         let uu____19224 = tc_modul env1 m b  in
         match uu____19224 with
         | (m1,env2) ->
             ((let uu____19236 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____19236
               then
                 let uu____19239 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____19239
               else ());
              (let uu____19245 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____19245
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
                         let uu____19283 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____19283 with
                         | (univnames1,e) ->
                             let uu___2642_19290 = lb  in
                             let uu____19291 =
                               let uu____19294 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____19294 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2642_19290.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2642_19290.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___2642_19290.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2642_19290.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____19291;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2642_19290.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2642_19290.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___2644_19295 = se  in
                       let uu____19296 =
                         let uu____19297 =
                           let uu____19304 =
                             let uu____19305 = FStar_List.map update lbs  in
                             (b1, uu____19305)  in
                           (uu____19304, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____19297  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____19296;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___2644_19295.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___2644_19295.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___2644_19295.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___2644_19295.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____19313 -> se  in
                 let normalized_module =
                   let uu___2648_19315 = m1  in
                   let uu____19316 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___2648_19315.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____19316;
                     FStar_Syntax_Syntax.exports =
                       (uu___2648_19315.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___2648_19315.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____19317 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____19317
               else ());
              (m1, env2)))
  