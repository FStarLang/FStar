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
       let signature =
         check_and_gen' "signature" Prims.int_one
           FStar_Pervasives_Native.None ed.FStar_Syntax_Syntax.signature
          in
       log_combinator "signature" signature;
       (let repr =
          check_and_gen' "repr" Prims.int_one FStar_Pervasives_Native.None
            ed.FStar_Syntax_Syntax.repr
           in
        log_combinator "repr" repr;
        (let fresh_a_and_u_a a =
           let uu____777 = FStar_Syntax_Util.type_u ()  in
           FStar_All.pipe_right uu____777
             (fun uu____794  ->
                match uu____794 with
                | (t,u) ->
                    let uu____805 =
                      let uu____806 =
                        FStar_Syntax_Syntax.gen_bv a
                          FStar_Pervasives_Native.None t
                         in
                      FStar_All.pipe_right uu____806
                        FStar_Syntax_Syntax.mk_binder
                       in
                    (uu____805, u))
            in
         let fresh_x_a x a =
           let uu____820 =
             let uu____821 =
               let uu____822 =
                 FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
               FStar_All.pipe_right uu____822 FStar_Syntax_Syntax.bv_to_name
                in
             FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
               uu____821
              in
           FStar_All.pipe_right uu____820 FStar_Syntax_Syntax.mk_binder  in
         let fresh_repr r env u a_bv =
           let signature1 =
             let uu____861 = signature  in
             match uu____861 with | (us,t,ty) -> (us, t)  in
           let fail1 t =
             let uu____885 =
               FStar_TypeChecker_Err.unexpected_signature_for_monad env0
                 ed.FStar_Syntax_Syntax.mname t
                in
             FStar_Errors.raise_error uu____885
               (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
              in
           let uu____899 = FStar_TypeChecker_Env.inst_tscheme signature1  in
           match uu____899 with
           | (uu____908,signature2) ->
               let uu____910 =
                 let uu____911 = FStar_Syntax_Subst.compress signature2  in
                 uu____911.FStar_Syntax_Syntax.n  in
               (match uu____910 with
                | FStar_Syntax_Syntax.Tm_arrow (bs,uu____919) ->
                    let bs1 = FStar_Syntax_Subst.open_binders bs  in
                    (match bs1 with
                     | a::is ->
                         let uu____967 =
                           let uu____978 =
                             let uu____989 =
                               let uu____992 =
                                 let uu____993 =
                                   let uu____1000 =
                                     FStar_Syntax_Syntax.bv_to_name a_bv  in
                                   ((FStar_Pervasives_Native.fst a),
                                     uu____1000)
                                    in
                                 FStar_Syntax_Syntax.NT uu____993  in
                               [uu____992]  in
                             ([], FStar_TypeChecker_Env.trivial_guard,
                               uu____989)
                              in
                           FStar_List.fold_left
                             (fun uu____1039  ->
                                fun uu____1040  ->
                                  match (uu____1039, uu____1040) with
                                  | ((is1,g,substs),(b,uu____1087)) ->
                                      let uu____1116 =
                                        let uu____1129 =
                                          FStar_Syntax_Subst.subst substs
                                            b.FStar_Syntax_Syntax.sort
                                           in
                                        FStar_TypeChecker_Util.new_implicit_var
                                          "" r env uu____1129
                                         in
                                      (match uu____1116 with
                                       | (t,uu____1142,g_t) ->
                                           let uu____1156 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g g_t
                                              in
                                           ((FStar_List.append is1 [t]),
                                             uu____1156,
                                             (FStar_List.append substs
                                                [FStar_Syntax_Syntax.NT
                                                   (b, t)])))) uu____978 is
                            in
                         (match uu____967 with
                          | (is1,g,uu____1169) ->
                              let repr_ts =
                                let uu____1179 = repr  in
                                match uu____1179 with
                                | (us,t,uu____1188) -> (us, t)  in
                              let repr1 =
                                let uu____1194 =
                                  FStar_TypeChecker_Env.inst_tscheme_with
                                    repr_ts [u]
                                   in
                                FStar_All.pipe_right uu____1194
                                  FStar_Pervasives_Native.snd
                                 in
                              let uu____1203 =
                                let uu____1204 =
                                  let uu____1209 =
                                    let uu____1210 =
                                      let uu____1213 =
                                        FStar_Syntax_Syntax.bv_to_name a_bv
                                         in
                                      uu____1213 :: is1  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1210
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app repr1
                                    uu____1209
                                   in
                                uu____1204 FStar_Pervasives_Native.None r  in
                              (uu____1203, g))
                     | uu____1222 -> fail1 signature2)
                | uu____1223 -> fail1 signature2)
            in
         let return_repr =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
              in
           let uu____1242 =
             check_and_gen' "return_repr" Prims.int_one
               FStar_Pervasives_Native.None
               ed.FStar_Syntax_Syntax.return_repr
              in
           match uu____1242 with
           | (ret_us,ret_t,ret_ty) ->
               let uu____1266 =
                 FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
               (match uu____1266 with
                | (us,ty) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                       in
                    let uu____1286 = fresh_a_and_u_a "a"  in
                    (match uu____1286 with
                     | (a,u_a) ->
                         let x_a = fresh_x_a "x" a  in
                         let rest_bs =
                           let uu____1317 =
                             let uu____1318 = FStar_Syntax_Subst.compress ty
                                in
                             uu____1318.FStar_Syntax_Syntax.n  in
                           match uu____1317 with
                           | FStar_Syntax_Syntax.Tm_arrow
                               ((a',uu____1330)::(x_a',uu____1332)::bs,uu____1334)
                               ->
                               let substs =
                                 let uu____1378 =
                                   let uu____1379 =
                                     let uu____1386 =
                                       FStar_Syntax_Syntax.bv_to_name
                                         (FStar_Pervasives_Native.fst a)
                                        in
                                     (a', uu____1386)  in
                                   FStar_Syntax_Syntax.NT uu____1379  in
                                 let uu____1393 =
                                   let uu____1396 =
                                     let uu____1397 =
                                       let uu____1404 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           (FStar_Pervasives_Native.fst x_a)
                                          in
                                       (x_a', uu____1404)  in
                                     FStar_Syntax_Syntax.NT uu____1397  in
                                   [uu____1396]  in
                                 uu____1378 :: uu____1393  in
                               FStar_Syntax_Subst.subst_binders substs bs
                           | uu____1411 ->
                               FStar_Errors.raise_error
                                 (FStar_Errors.Fatal_UnexpectedEffect, "") r
                            in
                         let bs = a :: x_a :: rest_bs  in
                         let uu____1443 =
                           let uu____1448 =
                             FStar_TypeChecker_Env.push_binders env bs  in
                           fresh_repr r uu____1448 u_a
                             (FStar_Pervasives_Native.fst a)
                            in
                         (match uu____1443 with
                          | (repr1,g) ->
                              let k =
                                let uu____1468 =
                                  FStar_Syntax_Syntax.mk_Total' repr1
                                    (FStar_Pervasives_Native.Some u_a)
                                   in
                                FStar_Syntax_Util.arrow bs uu____1468  in
                              let g_eq = FStar_TypeChecker_Rel.teq env ty k
                                 in
                              ((let uu____1473 =
                                  FStar_TypeChecker_Env.conj_guard g g_eq  in
                                FStar_TypeChecker_Rel.force_trivial_guard env
                                  uu____1473);
                               (let uu____1474 =
                                  FStar_Syntax_Subst.close_univ_vars us k  in
                                (ret_us, ret_t, uu____1474))))))
            in
         log_combinator "return_repr" return_repr;
         (let bind_repr =
            let r =
              (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
               in
            let uu____1503 =
              check_and_gen' "bind_repr" (Prims.of_int (2))
                FStar_Pervasives_Native.None ed.FStar_Syntax_Syntax.bind_repr
               in
            match uu____1503 with
            | (bind_us,bind_t,bind_ty) ->
                let uu____1527 =
                  FStar_Syntax_Subst.open_univ_vars bind_us bind_ty  in
                (match uu____1527 with
                 | (us,ty) ->
                     let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                        in
                     let uu____1547 = fresh_a_and_u_a "a"  in
                     (match uu____1547 with
                      | (a,u_a) ->
                          let uu____1567 = fresh_a_and_u_a "b"  in
                          (match uu____1567 with
                           | (b,u_b) ->
                               let rest_bs =
                                 let uu____1596 =
                                   let uu____1597 =
                                     FStar_Syntax_Subst.compress ty  in
                                   uu____1597.FStar_Syntax_Syntax.n  in
                                 match uu____1596 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     ((a',uu____1609)::(b',uu____1611)::bs,uu____1613)
                                     when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (2))
                                     ->
                                     let uu____1661 =
                                       FStar_List.splitAt
                                         ((FStar_List.length bs) -
                                            (Prims.of_int (2))) bs
                                        in
                                     (match uu____1661 with
                                      | (bs1,uu____1704) ->
                                          let substs =
                                            let uu____1740 =
                                              let uu____1741 =
                                                let uu____1748 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    (FStar_Pervasives_Native.fst
                                                       a)
                                                   in
                                                (a', uu____1748)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____1741
                                               in
                                            let uu____1755 =
                                              let uu____1758 =
                                                let uu____1759 =
                                                  let uu____1766 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         b)
                                                     in
                                                  (b', uu____1766)  in
                                                FStar_Syntax_Syntax.NT
                                                  uu____1759
                                                 in
                                              [uu____1758]  in
                                            uu____1740 :: uu____1755  in
                                          FStar_Syntax_Subst.subst_binders
                                            substs bs1)
                                 | uu____1773 ->
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_UnexpectedEffect,
                                         "") r
                                  in
                               let bs = a :: b :: rest_bs  in
                               let uu____1805 =
                                 let uu____1816 =
                                   let uu____1821 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   fresh_repr r uu____1821 u_a
                                     (FStar_Pervasives_Native.fst a)
                                    in
                                 match uu____1816 with
                                 | (repr1,g) ->
                                     let uu____1836 =
                                       let uu____1843 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None repr1
                                          in
                                       FStar_All.pipe_right uu____1843
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____1836, g)
                                  in
                               (match uu____1805 with
                                | (f,g_f) ->
                                    let uu____1883 =
                                      let x_a = fresh_x_a "x" a  in
                                      let uu____1896 =
                                        let uu____1901 =
                                          FStar_TypeChecker_Env.push_binders
                                            env (FStar_List.append bs [x_a])
                                           in
                                        fresh_repr r uu____1901 u_b
                                          (FStar_Pervasives_Native.fst b)
                                         in
                                      match uu____1896 with
                                      | (repr1,g) ->
                                          let uu____1934 =
                                            let uu____1941 =
                                              let uu____1942 =
                                                let uu____1943 =
                                                  FStar_Syntax_Syntax.mk_Total'
                                                    repr1
                                                    (FStar_Pervasives_Native.Some
                                                       u_b)
                                                   in
                                                FStar_Syntax_Util.arrow 
                                                  [x_a] uu____1943
                                                 in
                                              FStar_Syntax_Syntax.gen_bv "g"
                                                FStar_Pervasives_Native.None
                                                uu____1942
                                               in
                                            FStar_All.pipe_right uu____1941
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          (uu____1934, g)
                                       in
                                    (match uu____1883 with
                                     | (g,g_g) ->
                                         let uu____1997 =
                                           let uu____2002 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           fresh_repr r uu____2002 u_b
                                             (FStar_Pervasives_Native.fst b)
                                            in
                                         (match uu____1997 with
                                          | (repr1,g_repr) ->
                                              let k =
                                                let uu____2022 =
                                                  FStar_Syntax_Syntax.mk_Total'
                                                    repr1
                                                    (FStar_Pervasives_Native.Some
                                                       u_b)
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  (FStar_List.append bs
                                                     [f; g]) uu____2022
                                                 in
                                              let g_eq =
                                                FStar_TypeChecker_Rel.teq env
                                                  ty k
                                                 in
                                              ((let uu____2051 =
                                                  let uu____2056 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  FStar_TypeChecker_Rel.force_trivial_guard
                                                    uu____2056
                                                   in
                                                FStar_List.iter uu____2051
                                                  [g_f; g_g; g_repr; g_eq]);
                                               (let uu____2057 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    bind_us k
                                                   in
                                                (bind_us, bind_t, uu____2057)))))))))
             in
          log_combinator "bind_repr" bind_repr;
          failwith "That's it folks!";
          ed))))
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      (let uu____2082 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "ED")
          in
       if uu____2082
       then
         let uu____2087 = FStar_Syntax_Print.eff_decl_to_string false ed  in
         FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____2087
       else ());
      (let uu____2093 =
         let uu____2098 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____2098 with
         | (ed_univs_subst,ed_univs) ->
             let bs =
               let uu____2122 =
                 FStar_Syntax_Subst.subst_binders ed_univs_subst
                   ed.FStar_Syntax_Syntax.binders
                  in
               FStar_Syntax_Subst.open_binders uu____2122  in
             let uu____2123 =
               let uu____2130 =
                 FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
               FStar_TypeChecker_TcTerm.tc_tparams uu____2130 bs  in
             (match uu____2123 with
              | (bs1,uu____2136,uu____2137) ->
                  let uu____2138 =
                    let tmp_t =
                      let uu____2148 =
                        let uu____2151 =
                          FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                            (fun _2156  -> FStar_Pervasives_Native.Some _2156)
                           in
                        FStar_Syntax_Syntax.mk_Total'
                          FStar_Syntax_Syntax.t_unit uu____2151
                         in
                      FStar_Syntax_Util.arrow bs1 uu____2148  in
                    let uu____2157 =
                      FStar_TypeChecker_Util.generalize_universes env0 tmp_t
                       in
                    match uu____2157 with
                    | (us,tmp_t1) ->
                        let uu____2174 =
                          let uu____2175 =
                            let uu____2176 =
                              FStar_All.pipe_right tmp_t1
                                FStar_Syntax_Util.arrow_formals
                               in
                            FStar_All.pipe_right uu____2176
                              FStar_Pervasives_Native.fst
                             in
                          FStar_All.pipe_right uu____2175
                            FStar_Syntax_Subst.close_binders
                           in
                        (us, uu____2174)
                     in
                  (match uu____2138 with
                   | (us,bs2) ->
                       (match ed_univs with
                        | [] -> (us, bs2)
                        | uu____2245 ->
                            let uu____2248 =
                              ((FStar_List.length ed_univs) =
                                 (FStar_List.length us))
                                &&
                                (FStar_List.forall2
                                   (fun u1  ->
                                      fun u2  ->
                                        let uu____2255 =
                                          FStar_Syntax_Syntax.order_univ_name
                                            u1 u2
                                           in
                                        uu____2255 = Prims.int_zero) ed_univs
                                   us)
                               in
                            if uu____2248
                            then (us, bs2)
                            else
                              (let uu____2266 =
                                 let uu____2272 =
                                   let uu____2274 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length ed_univs)
                                      in
                                   let uu____2276 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length us)
                                      in
                                   FStar_Util.format3
                                     "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                     uu____2274 uu____2276
                                    in
                                 (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                   uu____2272)
                                  in
                               let uu____2280 =
                                 FStar_Ident.range_of_lid
                                   ed.FStar_Syntax_Syntax.mname
                                  in
                               FStar_Errors.raise_error uu____2266 uu____2280))))
          in
       match uu____2093 with
       | (us,bs) ->
           let ed1 =
             let uu___297_2288 = ed  in
             {
               FStar_Syntax_Syntax.is_layered =
                 (uu___297_2288.FStar_Syntax_Syntax.is_layered);
               FStar_Syntax_Syntax.cattributes =
                 (uu___297_2288.FStar_Syntax_Syntax.cattributes);
               FStar_Syntax_Syntax.mname =
                 (uu___297_2288.FStar_Syntax_Syntax.mname);
               FStar_Syntax_Syntax.univs = us;
               FStar_Syntax_Syntax.binders = bs;
               FStar_Syntax_Syntax.signature =
                 (uu___297_2288.FStar_Syntax_Syntax.signature);
               FStar_Syntax_Syntax.ret_wp =
                 (uu___297_2288.FStar_Syntax_Syntax.ret_wp);
               FStar_Syntax_Syntax.bind_wp =
                 (uu___297_2288.FStar_Syntax_Syntax.bind_wp);
               FStar_Syntax_Syntax.stronger =
                 (uu___297_2288.FStar_Syntax_Syntax.stronger);
               FStar_Syntax_Syntax.match_wps =
                 (uu___297_2288.FStar_Syntax_Syntax.match_wps);
               FStar_Syntax_Syntax.trivial =
                 (uu___297_2288.FStar_Syntax_Syntax.trivial);
               FStar_Syntax_Syntax.repr =
                 (uu___297_2288.FStar_Syntax_Syntax.repr);
               FStar_Syntax_Syntax.return_repr =
                 (uu___297_2288.FStar_Syntax_Syntax.return_repr);
               FStar_Syntax_Syntax.bind_repr =
                 (uu___297_2288.FStar_Syntax_Syntax.bind_repr);
               FStar_Syntax_Syntax.stronger_repr =
                 (uu___297_2288.FStar_Syntax_Syntax.stronger_repr);
               FStar_Syntax_Syntax.actions =
                 (uu___297_2288.FStar_Syntax_Syntax.actions);
               FStar_Syntax_Syntax.eff_attrs =
                 (uu___297_2288.FStar_Syntax_Syntax.eff_attrs)
             }  in
           let uu____2289 = FStar_Syntax_Subst.univ_var_opening us  in
           (match uu____2289 with
            | (ed_univs_subst,ed_univs) ->
                let uu____2308 =
                  let uu____2313 =
                    FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                  FStar_Syntax_Subst.open_binders' uu____2313  in
                (match uu____2308 with
                 | (ed_bs,ed_bs_subst) ->
                     let ed2 =
                       let op uu____2334 =
                         match uu____2334 with
                         | (us1,t) ->
                             let t1 =
                               let uu____2354 =
                                 FStar_Syntax_Subst.shift_subst
                                   ((FStar_List.length ed_bs) +
                                      (FStar_List.length us1)) ed_univs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____2354 t  in
                             let uu____2363 =
                               let uu____2364 =
                                 FStar_Syntax_Subst.shift_subst
                                   (FStar_List.length us1) ed_bs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____2364 t1  in
                             (us1, uu____2363)
                          in
                       let uu___311_2369 = ed1  in
                       let uu____2370 = op ed1.FStar_Syntax_Syntax.signature
                          in
                       let uu____2371 = op ed1.FStar_Syntax_Syntax.ret_wp  in
                       let uu____2372 = op ed1.FStar_Syntax_Syntax.bind_wp
                          in
                       let uu____2373 = op ed1.FStar_Syntax_Syntax.stronger
                          in
                       let uu____2374 =
                         FStar_Syntax_Util.map_match_wps op
                           ed1.FStar_Syntax_Syntax.match_wps
                          in
                       let uu____2379 =
                         FStar_Util.map_opt ed1.FStar_Syntax_Syntax.trivial
                           op
                          in
                       let uu____2382 = op ed1.FStar_Syntax_Syntax.repr  in
                       let uu____2383 =
                         op ed1.FStar_Syntax_Syntax.return_repr  in
                       let uu____2384 = op ed1.FStar_Syntax_Syntax.bind_repr
                          in
                       let uu____2385 =
                         FStar_List.map
                           (fun a  ->
                              let uu___314_2393 = a  in
                              let uu____2394 =
                                let uu____2395 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_defn))
                                   in
                                FStar_Pervasives_Native.snd uu____2395  in
                              let uu____2406 =
                                let uu____2407 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_typ))
                                   in
                                FStar_Pervasives_Native.snd uu____2407  in
                              {
                                FStar_Syntax_Syntax.action_name =
                                  (uu___314_2393.FStar_Syntax_Syntax.action_name);
                                FStar_Syntax_Syntax.action_unqualified_name =
                                  (uu___314_2393.FStar_Syntax_Syntax.action_unqualified_name);
                                FStar_Syntax_Syntax.action_univs =
                                  (uu___314_2393.FStar_Syntax_Syntax.action_univs);
                                FStar_Syntax_Syntax.action_params =
                                  (uu___314_2393.FStar_Syntax_Syntax.action_params);
                                FStar_Syntax_Syntax.action_defn = uu____2394;
                                FStar_Syntax_Syntax.action_typ = uu____2406
                              }) ed1.FStar_Syntax_Syntax.actions
                          in
                       {
                         FStar_Syntax_Syntax.is_layered =
                           (uu___311_2369.FStar_Syntax_Syntax.is_layered);
                         FStar_Syntax_Syntax.cattributes =
                           (uu___311_2369.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.mname =
                           (uu___311_2369.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.univs =
                           (uu___311_2369.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___311_2369.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature = uu____2370;
                         FStar_Syntax_Syntax.ret_wp = uu____2371;
                         FStar_Syntax_Syntax.bind_wp = uu____2372;
                         FStar_Syntax_Syntax.stronger = uu____2373;
                         FStar_Syntax_Syntax.match_wps = uu____2374;
                         FStar_Syntax_Syntax.trivial = uu____2379;
                         FStar_Syntax_Syntax.repr = uu____2382;
                         FStar_Syntax_Syntax.return_repr = uu____2383;
                         FStar_Syntax_Syntax.bind_repr = uu____2384;
                         FStar_Syntax_Syntax.stronger_repr =
                           FStar_Pervasives_Native.None;
                         FStar_Syntax_Syntax.actions = uu____2385;
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___311_2369.FStar_Syntax_Syntax.eff_attrs)
                       }  in
                     ((let uu____2419 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env0)
                           (FStar_Options.Other "ED")
                          in
                       if uu____2419
                       then
                         let uu____2424 =
                           FStar_Syntax_Print.eff_decl_to_string false ed2
                            in
                         FStar_Util.print1
                           "After typechecking binders eff_decl: \n\t%s\n"
                           uu____2424
                       else ());
                      (let env =
                         let uu____2431 =
                           FStar_TypeChecker_Env.push_univ_vars env0 ed_univs
                            in
                         FStar_TypeChecker_Env.push_binders uu____2431 ed_bs
                          in
                       let check_and_gen' comb n1 env_opt uu____2466 k =
                         match uu____2466 with
                         | (us1,t) ->
                             let env1 =
                               if FStar_Util.is_some env_opt
                               then
                                 FStar_All.pipe_right env_opt FStar_Util.must
                               else env  in
                             let uu____2486 =
                               FStar_Syntax_Subst.open_univ_vars us1 t  in
                             (match uu____2486 with
                              | (us2,t1) ->
                                  let t2 =
                                    match k with
                                    | FStar_Pervasives_Native.Some k1 ->
                                        let uu____2495 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env1 us2
                                           in
                                        tc_check_trivial_guard uu____2495 t1
                                          k1
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____2496 =
                                          let uu____2503 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            uu____2503 t1
                                           in
                                        (match uu____2496 with
                                         | (t2,uu____2505,g) ->
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env1 g;
                                              t2))
                                     in
                                  let uu____2508 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env1 t2
                                     in
                                  (match uu____2508 with
                                   | (g_us,t3) ->
                                       (if (FStar_List.length g_us) <> n1
                                        then
                                          (let error =
                                             let uu____2524 =
                                               FStar_Util.string_of_int n1
                                                in
                                             let uu____2526 =
                                               let uu____2528 =
                                                 FStar_All.pipe_right g_us
                                                   FStar_List.length
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2528
                                                 FStar_Util.string_of_int
                                                in
                                             FStar_Util.format4
                                               "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                               (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                               comb uu____2524 uu____2526
                                              in
                                           FStar_Errors.raise_error
                                             (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                               error)
                                             t3.FStar_Syntax_Syntax.pos)
                                        else ();
                                        (match us2 with
                                         | [] -> (g_us, t3)
                                         | uu____2543 ->
                                             let uu____2544 =
                                               ((FStar_List.length us2) =
                                                  (FStar_List.length g_us))
                                                 &&
                                                 (FStar_List.forall2
                                                    (fun u1  ->
                                                       fun u2  ->
                                                         let uu____2551 =
                                                           FStar_Syntax_Syntax.order_univ_name
                                                             u1 u2
                                                            in
                                                         uu____2551 =
                                                           Prims.int_zero)
                                                    us2 g_us)
                                                in
                                             if uu____2544
                                             then (g_us, t3)
                                             else
                                               (let uu____2562 =
                                                  let uu____2568 =
                                                    let uu____2570 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           us2)
                                                       in
                                                    let uu____2572 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           g_us)
                                                       in
                                                    FStar_Util.format4
                                                      "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                      (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      comb uu____2570
                                                      uu____2572
                                                     in
                                                  (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                    uu____2568)
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____2562
                                                  t3.FStar_Syntax_Syntax.pos)))))
                          in
                       let signature =
                         check_and_gen' "signature" Prims.int_one
                           FStar_Pervasives_Native.None
                           ed2.FStar_Syntax_Syntax.signature
                           FStar_Pervasives_Native.None
                          in
                       (let uu____2580 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env0)
                            (FStar_Options.Other "ED")
                           in
                        if uu____2580
                        then
                          let uu____2585 =
                            FStar_Syntax_Print.tscheme_to_string signature
                             in
                          FStar_Util.print1 "Typechecked signature: %s\n"
                            uu____2585
                        else ());
                       (let fresh_a_and_wp uu____2601 =
                          let fail1 t =
                            let uu____2614 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env ed2.FStar_Syntax_Syntax.mname t
                               in
                            FStar_Errors.raise_error uu____2614
                              (FStar_Pervasives_Native.snd
                                 ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                             in
                          let uu____2630 =
                            FStar_TypeChecker_Env.inst_tscheme signature  in
                          match uu____2630 with
                          | (uu____2641,signature1) ->
                              let uu____2643 =
                                let uu____2644 =
                                  FStar_Syntax_Subst.compress signature1  in
                                uu____2644.FStar_Syntax_Syntax.n  in
                              (match uu____2643 with
                               | FStar_Syntax_Syntax.Tm_arrow
                                   (bs1,uu____2654) ->
                                   let bs2 =
                                     FStar_Syntax_Subst.open_binders bs1  in
                                   (match bs2 with
                                    | (a,uu____2683)::(wp,uu____2685)::[] ->
                                        (a, (wp.FStar_Syntax_Syntax.sort))
                                    | uu____2714 -> fail1 signature1)
                               | uu____2715 -> fail1 signature1)
                           in
                        let log_combinator s ts =
                          let uu____2729 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "ED")
                             in
                          if uu____2729
                          then
                            let uu____2734 =
                              FStar_Syntax_Print.tscheme_to_string ts  in
                            FStar_Util.print3 "Typechecked %s:%s = %s\n"
                              (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                              s uu____2734
                          else ()  in
                        let ret_wp =
                          let uu____2740 = fresh_a_and_wp ()  in
                          match uu____2740 with
                          | (a,wp_sort) ->
                              let k =
                                let uu____2756 =
                                  let uu____2765 =
                                    FStar_Syntax_Syntax.mk_binder a  in
                                  let uu____2772 =
                                    let uu____2781 =
                                      let uu____2788 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      FStar_Syntax_Syntax.null_binder
                                        uu____2788
                                       in
                                    [uu____2781]  in
                                  uu____2765 :: uu____2772  in
                                let uu____2807 =
                                  FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                FStar_Syntax_Util.arrow uu____2756 uu____2807
                                 in
                              check_and_gen' "ret_wp" Prims.int_one
                                FStar_Pervasives_Native.None
                                ed2.FStar_Syntax_Syntax.ret_wp
                                (FStar_Pervasives_Native.Some k)
                           in
                        log_combinator "ret_wp" ret_wp;
                        (let bind_wp =
                           let uu____2815 = fresh_a_and_wp ()  in
                           match uu____2815 with
                           | (a,wp_sort_a) ->
                               let uu____2828 = fresh_a_and_wp ()  in
                               (match uu____2828 with
                                | (b,wp_sort_b) ->
                                    let wp_sort_a_b =
                                      let uu____2844 =
                                        let uu____2853 =
                                          let uu____2860 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____2860
                                           in
                                        [uu____2853]  in
                                      let uu____2873 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____2844
                                        uu____2873
                                       in
                                    let k =
                                      let uu____2879 =
                                        let uu____2888 =
                                          FStar_Syntax_Syntax.null_binder
                                            FStar_Syntax_Syntax.t_range
                                           in
                                        let uu____2895 =
                                          let uu____2904 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____2911 =
                                            let uu____2920 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____2927 =
                                              let uu____2936 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              let uu____2943 =
                                                let uu____2952 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a_b
                                                   in
                                                [uu____2952]  in
                                              uu____2936 :: uu____2943  in
                                            uu____2920 :: uu____2927  in
                                          uu____2904 :: uu____2911  in
                                        uu____2888 :: uu____2895  in
                                      let uu____2995 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____2879
                                        uu____2995
                                       in
                                    check_and_gen' "bind_wp"
                                      (Prims.of_int (2))
                                      FStar_Pervasives_Native.None
                                      ed2.FStar_Syntax_Syntax.bind_wp
                                      (FStar_Pervasives_Native.Some k))
                            in
                         log_combinator "bind_wp" bind_wp;
                         (let stronger =
                            let uu____3003 = fresh_a_and_wp ()  in
                            match uu____3003 with
                            | (a,wp_sort_a) ->
                                let uu____3016 = FStar_Syntax_Util.type_u ()
                                   in
                                (match uu____3016 with
                                 | (t,uu____3022) ->
                                     let k =
                                       let uu____3026 =
                                         let uu____3035 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____3042 =
                                           let uu____3051 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____3058 =
                                             let uu____3067 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____3067]  in
                                           uu____3051 :: uu____3058  in
                                         uu____3035 :: uu____3042  in
                                       let uu____3098 =
                                         FStar_Syntax_Syntax.mk_Total t  in
                                       FStar_Syntax_Util.arrow uu____3026
                                         uu____3098
                                        in
                                     check_and_gen' "stronger" Prims.int_one
                                       FStar_Pervasives_Native.None
                                       ed2.FStar_Syntax_Syntax.stronger
                                       (FStar_Pervasives_Native.Some k))
                             in
                          log_combinator "stronger" stronger;
                          (let match_wps =
                             let uu____3110 =
                               FStar_Syntax_Util.get_match_with_close_wps
                                 ed2.FStar_Syntax_Syntax.match_wps
                                in
                             match uu____3110 with
                             | (if_then_else1,ite_wp,close_wp) ->
                                 let if_then_else2 =
                                   let uu____3125 = fresh_a_and_wp ()  in
                                   match uu____3125 with
                                   | (a,wp_sort_a) ->
                                       let p =
                                         let uu____3139 =
                                           let uu____3142 =
                                             FStar_Ident.range_of_lid
                                               ed2.FStar_Syntax_Syntax.mname
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____3142
                                            in
                                         let uu____3143 =
                                           let uu____3144 =
                                             FStar_Syntax_Util.type_u ()  in
                                           FStar_All.pipe_right uu____3144
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____3139 uu____3143
                                          in
                                       let k =
                                         let uu____3156 =
                                           let uu____3165 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____3172 =
                                             let uu____3181 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 p
                                                in
                                             let uu____3188 =
                                               let uu____3197 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               let uu____3204 =
                                                 let uu____3213 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____3213]  in
                                               uu____3197 :: uu____3204  in
                                             uu____3181 :: uu____3188  in
                                           uu____3165 :: uu____3172  in
                                         let uu____3250 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a
                                            in
                                         FStar_Syntax_Util.arrow uu____3156
                                           uu____3250
                                          in
                                       check_and_gen' "if_then_else"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         if_then_else1
                                         (FStar_Pervasives_Native.Some k)
                                    in
                                 (log_combinator "if_then_else" if_then_else2;
                                  (let ite_wp1 =
                                     let uu____3258 = fresh_a_and_wp ()  in
                                     match uu____3258 with
                                     | (a,wp_sort_a) ->
                                         let k =
                                           let uu____3274 =
                                             let uu____3283 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____3290 =
                                               let uu____3299 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____3299]  in
                                             uu____3283 :: uu____3290  in
                                           let uu____3324 =
                                             FStar_Syntax_Syntax.mk_Total
                                               wp_sort_a
                                              in
                                           FStar_Syntax_Util.arrow uu____3274
                                             uu____3324
                                            in
                                         check_and_gen' "ite_wp"
                                           Prims.int_one
                                           FStar_Pervasives_Native.None
                                           ite_wp
                                           (FStar_Pervasives_Native.Some k)
                                      in
                                   log_combinator "ite_wp" ite_wp1;
                                   (let close_wp1 =
                                      let uu____3332 = fresh_a_and_wp ()  in
                                      match uu____3332 with
                                      | (a,wp_sort_a) ->
                                          let b =
                                            let uu____3346 =
                                              let uu____3349 =
                                                FStar_Ident.range_of_lid
                                                  ed2.FStar_Syntax_Syntax.mname
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____3349
                                               in
                                            let uu____3350 =
                                              let uu____3351 =
                                                FStar_Syntax_Util.type_u ()
                                                 in
                                              FStar_All.pipe_right uu____3351
                                                FStar_Pervasives_Native.fst
                                               in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____3346 uu____3350
                                             in
                                          let wp_sort_b_a =
                                            let uu____3363 =
                                              let uu____3372 =
                                                let uu____3379 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    b
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____3379
                                                 in
                                              [uu____3372]  in
                                            let uu____3392 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____3363 uu____3392
                                             in
                                          let k =
                                            let uu____3398 =
                                              let uu____3407 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____3414 =
                                                let uu____3423 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    b
                                                   in
                                                let uu____3430 =
                                                  let uu____3439 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_b_a
                                                     in
                                                  [uu____3439]  in
                                                uu____3423 :: uu____3430  in
                                              uu____3407 :: uu____3414  in
                                            let uu____3470 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____3398 uu____3470
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
                             let uu____3480 = fresh_a_and_wp ()  in
                             match uu____3480 with
                             | (a,wp_sort_a) ->
                                 let uu____3495 = FStar_Syntax_Util.type_u ()
                                    in
                                 (match uu____3495 with
                                  | (t,uu____3503) ->
                                      let k =
                                        let uu____3507 =
                                          let uu____3516 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____3523 =
                                            let uu____3532 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_sort_a
                                               in
                                            [uu____3532]  in
                                          uu____3516 :: uu____3523  in
                                        let uu____3557 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____3507
                                          uu____3557
                                         in
                                      let trivial =
                                        let uu____3561 =
                                          FStar_All.pipe_right
                                            ed2.FStar_Syntax_Syntax.trivial
                                            FStar_Util.must
                                           in
                                        check_and_gen' "trivial"
                                          Prims.int_one
                                          FStar_Pervasives_Native.None
                                          uu____3561
                                          (FStar_Pervasives_Native.Some k)
                                         in
                                      (log_combinator "trivial" trivial;
                                       FStar_Pervasives_Native.Some trivial))
                              in
                           let uu____3576 =
                             let uu____3587 =
                               let uu____3588 =
                                 FStar_Syntax_Subst.compress
                                   (FStar_Pervasives_Native.snd
                                      ed2.FStar_Syntax_Syntax.repr)
                                  in
                               uu____3588.FStar_Syntax_Syntax.n  in
                             match uu____3587 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____3607 ->
                                 let repr =
                                   let uu____3609 = fresh_a_and_wp ()  in
                                   match uu____3609 with
                                   | (a,wp_sort_a) ->
                                       let uu____3622 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____3622 with
                                        | (t,uu____3628) ->
                                            let k =
                                              let uu____3632 =
                                                let uu____3641 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____3648 =
                                                  let uu____3657 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a
                                                     in
                                                  [uu____3657]  in
                                                uu____3641 :: uu____3648  in
                                              let uu____3682 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____3632 uu____3682
                                               in
                                            check_and_gen' "repr"
                                              Prims.int_one
                                              FStar_Pervasives_Native.None
                                              ed2.FStar_Syntax_Syntax.repr
                                              (FStar_Pervasives_Native.Some k))
                                    in
                                 (log_combinator "repr" repr;
                                  (let mk_repr' t wp =
                                     let uu____3702 =
                                       FStar_TypeChecker_Env.inst_tscheme
                                         repr
                                        in
                                     match uu____3702 with
                                     | (uu____3709,repr1) ->
                                         let repr2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.EraseUniverses;
                                             FStar_TypeChecker_Env.AllowUnboundUniverses]
                                             env repr1
                                            in
                                         let uu____3712 =
                                           let uu____3719 =
                                             let uu____3720 =
                                               let uu____3737 =
                                                 let uu____3748 =
                                                   FStar_All.pipe_right t
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____3765 =
                                                   let uu____3776 =
                                                     FStar_All.pipe_right wp
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____3776]  in
                                                 uu____3748 :: uu____3765  in
                                               (repr2, uu____3737)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3720
                                              in
                                           FStar_Syntax_Syntax.mk uu____3719
                                            in
                                         uu____3712
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                      in
                                   let mk_repr a wp =
                                     let uu____3842 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     mk_repr' uu____3842 wp  in
                                   let destruct_repr t =
                                     let uu____3857 =
                                       let uu____3858 =
                                         FStar_Syntax_Subst.compress t  in
                                       uu____3858.FStar_Syntax_Syntax.n  in
                                     match uu____3857 with
                                     | FStar_Syntax_Syntax.Tm_app
                                         (uu____3869,(t1,uu____3871)::
                                          (wp,uu____3873)::[])
                                         -> (t1, wp)
                                     | uu____3932 ->
                                         failwith "Unexpected repr type"
                                      in
                                   let return_repr =
                                     let uu____3943 = fresh_a_and_wp ()  in
                                     match uu____3943 with
                                     | (a,uu____3951) ->
                                         let x_a =
                                           let uu____3957 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x_a"
                                             FStar_Pervasives_Native.None
                                             uu____3957
                                            in
                                         let res =
                                           let wp =
                                             let uu____3965 =
                                               let uu____3970 =
                                                 let uu____3971 =
                                                   FStar_TypeChecker_Env.inst_tscheme
                                                     ret_wp
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3971
                                                   FStar_Pervasives_Native.snd
                                                  in
                                               let uu____3980 =
                                                 let uu____3981 =
                                                   let uu____3990 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3990
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____3999 =
                                                   let uu____4010 =
                                                     let uu____4019 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         x_a
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____4019
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____4010]  in
                                                 uu____3981 :: uu____3999  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____3970 uu____3980
                                                in
                                             uu____3965
                                               FStar_Pervasives_Native.None
                                               FStar_Range.dummyRange
                                              in
                                           mk_repr a wp  in
                                         let k =
                                           let uu____4055 =
                                             let uu____4064 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____4071 =
                                               let uu____4080 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   x_a
                                                  in
                                               [uu____4080]  in
                                             uu____4064 :: uu____4071  in
                                           let uu____4105 =
                                             FStar_Syntax_Syntax.mk_Total res
                                              in
                                           FStar_Syntax_Util.arrow uu____4055
                                             uu____4105
                                            in
                                         let uu____4108 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env k
                                            in
                                         (match uu____4108 with
                                          | (k1,uu____4116,uu____4117) ->
                                              let env1 =
                                                let uu____4121 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env
                                                    (FStar_Pervasives_Native.snd
                                                       ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____4121
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
                                        let uu____4132 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            FStar_Parser_Const.range_0
                                            FStar_Syntax_Syntax.delta_constant
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_All.pipe_right uu____4132
                                          FStar_Syntax_Syntax.fv_to_tm
                                         in
                                      let uu____4133 = fresh_a_and_wp ()  in
                                      match uu____4133 with
                                      | (a,wp_sort_a) ->
                                          let uu____4146 = fresh_a_and_wp ()
                                             in
                                          (match uu____4146 with
                                           | (b,wp_sort_b) ->
                                               let wp_sort_a_b =
                                                 let uu____4162 =
                                                   let uu____4171 =
                                                     let uu____4178 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____4178
                                                      in
                                                   [uu____4171]  in
                                                 let uu____4191 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     wp_sort_b
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____4162 uu____4191
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
                                                 let uu____4199 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     a
                                                    in
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "x_a"
                                                   FStar_Pervasives_Native.None
                                                   uu____4199
                                                  in
                                               let wp_g_x =
                                                 let uu____4204 =
                                                   let uu____4209 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       wp_g
                                                      in
                                                   let uu____4210 =
                                                     let uu____4211 =
                                                       let uu____4220 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x_a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____4220
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____4211]  in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     uu____4209 uu____4210
                                                    in
                                                 uu____4204
                                                   FStar_Pervasives_Native.None
                                                   FStar_Range.dummyRange
                                                  in
                                               let res =
                                                 let wp =
                                                   let uu____4251 =
                                                     let uu____4256 =
                                                       let uu____4257 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           bind_wp
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____4257
                                                         FStar_Pervasives_Native.snd
                                                        in
                                                     let uu____4266 =
                                                       let uu____4267 =
                                                         let uu____4270 =
                                                           let uu____4273 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               a
                                                              in
                                                           let uu____4274 =
                                                             let uu____4277 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 b
                                                                in
                                                             let uu____4278 =
                                                               let uu____4281
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_f
                                                                  in
                                                               let uu____4282
                                                                 =
                                                                 let uu____4285
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g
                                                                    in
                                                                 [uu____4285]
                                                                  in
                                                               uu____4281 ::
                                                                 uu____4282
                                                                in
                                                             uu____4277 ::
                                                               uu____4278
                                                              in
                                                           uu____4273 ::
                                                             uu____4274
                                                            in
                                                         r :: uu____4270  in
                                                       FStar_List.map
                                                         FStar_Syntax_Syntax.as_arg
                                                         uu____4267
                                                        in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____4256 uu____4266
                                                      in
                                                   uu____4251
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 mk_repr b wp  in
                                               let maybe_range_arg =
                                                 let uu____4303 =
                                                   FStar_Util.for_some
                                                     (FStar_Syntax_Util.attr_eq
                                                        FStar_Syntax_Util.dm4f_bind_range_attr)
                                                     ed2.FStar_Syntax_Syntax.eff_attrs
                                                    in
                                                 if uu____4303
                                                 then
                                                   let uu____4314 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       FStar_Syntax_Syntax.t_range
                                                      in
                                                   let uu____4321 =
                                                     let uu____4330 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         FStar_Syntax_Syntax.t_range
                                                        in
                                                     [uu____4330]  in
                                                   uu____4314 :: uu____4321
                                                 else []  in
                                               let k =
                                                 let uu____4366 =
                                                   let uu____4375 =
                                                     let uu____4384 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____4391 =
                                                       let uu____4400 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           b
                                                          in
                                                       [uu____4400]  in
                                                     uu____4384 :: uu____4391
                                                      in
                                                   let uu____4425 =
                                                     let uu____4434 =
                                                       let uu____4443 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           wp_f
                                                          in
                                                       let uu____4450 =
                                                         let uu____4459 =
                                                           let uu____4466 =
                                                             let uu____4467 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp_f
                                                                in
                                                             mk_repr a
                                                               uu____4467
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____4466
                                                            in
                                                         let uu____4468 =
                                                           let uu____4477 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               wp_g
                                                              in
                                                           let uu____4484 =
                                                             let uu____4493 =
                                                               let uu____4500
                                                                 =
                                                                 let uu____4501
                                                                   =
                                                                   let uu____4510
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                   [uu____4510]
                                                                    in
                                                                 let uu____4529
                                                                   =
                                                                   let uu____4532
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                   FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____4532
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   uu____4501
                                                                   uu____4529
                                                                  in
                                                               FStar_Syntax_Syntax.null_binder
                                                                 uu____4500
                                                                in
                                                             [uu____4493]  in
                                                           uu____4477 ::
                                                             uu____4484
                                                            in
                                                         uu____4459 ::
                                                           uu____4468
                                                          in
                                                       uu____4443 ::
                                                         uu____4450
                                                        in
                                                     FStar_List.append
                                                       maybe_range_arg
                                                       uu____4434
                                                      in
                                                   FStar_List.append
                                                     uu____4375 uu____4425
                                                    in
                                                 let uu____4577 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     res
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____4366 uu____4577
                                                  in
                                               let uu____4580 =
                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                   env k
                                                  in
                                               (match uu____4580 with
                                                | (k1,uu____4588,uu____4589)
                                                    ->
                                                    let env1 =
                                                      FStar_TypeChecker_Env.set_range
                                                        env
                                                        (FStar_Pervasives_Native.snd
                                                           ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                       in
                                                    let env2 =
                                                      FStar_All.pipe_right
                                                        (let uu___512_4601 =
                                                           env1  in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.instantiate_imp);
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             = true;
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.nbe);
                                                           FStar_TypeChecker_Env.strict_args_tab
                                                             =
                                                             (uu___512_4601.FStar_TypeChecker_Env.strict_args_tab)
                                                         })
                                                        (fun _4603  ->
                                                           FStar_Pervasives_Native.Some
                                                             _4603)
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
                                         (let uu____4630 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env, act)
                                            else
                                              (let uu____4644 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____4644 with
                                               | (usubst,uvs) ->
                                                   let uu____4667 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env uvs
                                                      in
                                                   let uu____4668 =
                                                     let uu___525_4669 = act
                                                        in
                                                     let uu____4670 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____4671 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___525_4669.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___525_4669.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___525_4669.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____4670;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____4671
                                                     }  in
                                                   (uu____4667, uu____4668))
                                             in
                                          match uu____4630 with
                                          | (env1,act1) ->
                                              let act_typ =
                                                let uu____4675 =
                                                  let uu____4676 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  uu____4676.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____4675 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs1,c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c
                                                       in
                                                    let uu____4702 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname
                                                       in
                                                    if uu____4702
                                                    then
                                                      let uu____4705 =
                                                        let uu____4708 =
                                                          let uu____4709 =
                                                            let uu____4710 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____4710
                                                             in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____4709
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____4708
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____4705
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____4733 ->
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              let uu____4734 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env1 act_typ
                                                 in
                                              (match uu____4734 with
                                               | (act_typ1,uu____4742,g_t) ->
                                                   let env' =
                                                     let uu___542_4745 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env1 act_typ1
                                                        in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_sig
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.gamma_sig);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.attrtab
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.attrtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.phase1
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.phase1);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.uvar_subtyping
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.uvar_subtyping);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.fv_delta_depths
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.fv_delta_depths);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.postprocess
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.postprocess);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.nbe
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.nbe);
                                                       FStar_TypeChecker_Env.strict_args_tab
                                                         =
                                                         (uu___542_4745.FStar_TypeChecker_Env.strict_args_tab)
                                                     }  in
                                                   ((let uu____4748 =
                                                       FStar_TypeChecker_Env.debug
                                                         env1
                                                         (FStar_Options.Other
                                                            "ED")
                                                        in
                                                     if uu____4748
                                                     then
                                                       let uu____4752 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name
                                                          in
                                                       let uu____4754 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____4756 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1
                                                          in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____4752
                                                         uu____4754
                                                         uu____4756
                                                     else ());
                                                    (let uu____4761 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     match uu____4761 with
                                                     | (act_defn,uu____4769,g_a)
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
                                                         let uu____4773 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2
                                                              in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs1,c) ->
                                                               let uu____4809
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs1 c
                                                                  in
                                                               (match uu____4809
                                                                with
                                                                | (bs2,uu____4821)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____4828
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____4828
                                                                     in
                                                                    let uu____4831
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____4831
                                                                    with
                                                                    | 
                                                                    (k1,uu____4845,g)
                                                                    ->
                                                                    (k1, g)))
                                                           | uu____4849 ->
                                                               let uu____4850
                                                                 =
                                                                 let uu____4856
                                                                   =
                                                                   let uu____4858
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                   let uu____4860
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____4858
                                                                    uu____4860
                                                                    in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____4856)
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____4850
                                                                 act_defn1.FStar_Syntax_Syntax.pos
                                                            in
                                                         (match uu____4773
                                                          with
                                                          | (expected_k,g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env1
                                                                  act_typ2
                                                                  expected_k
                                                                 in
                                                              ((let uu____4878
                                                                  =
                                                                  let uu____4879
                                                                    =
                                                                    let uu____4880
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____4880
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____4879
                                                                   in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env1
                                                                  uu____4878);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____4882
                                                                    =
                                                                    let uu____4883
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____4883.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____4882
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____4908
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____4908
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____4915
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____4915
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____4935
                                                                    =
                                                                    let uu____4936
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____4936]
                                                                     in
                                                                    let uu____4937
                                                                    =
                                                                    let uu____4948
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____4948]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____4935;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____4937;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____4973
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____4973))
                                                                  | uu____4976
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                   in
                                                                let uu____4978
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
                                                                    let uu____5000
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____5000))
                                                                   in
                                                                match uu____4978
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
                                                                    let uu___592_5019
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___592_5019.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___592_5019.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___592_5019.FStar_Syntax_Syntax.action_params);
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
                           match uu____3576 with
                           | (repr,return_repr,bind_repr,actions) ->
                               let cl ts =
                                 let ts1 =
                                   FStar_Syntax_Subst.close_tscheme ed_bs ts
                                    in
                                 let ed_univs_closing =
                                   FStar_Syntax_Subst.univ_var_closing
                                     ed_univs
                                    in
                                 let uu____5044 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length ed_bs)
                                     ed_univs_closing
                                    in
                                 FStar_Syntax_Subst.subst_tscheme uu____5044
                                   ts1
                                  in
                               let ed3 =
                                 let uu___604_5054 = ed2  in
                                 let uu____5055 = cl signature  in
                                 let uu____5056 = cl ret_wp  in
                                 let uu____5057 = cl bind_wp  in
                                 let uu____5058 = cl stronger  in
                                 let uu____5059 =
                                   FStar_Syntax_Util.map_match_wps cl
                                     match_wps
                                    in
                                 let uu____5064 =
                                   FStar_Util.map_opt trivial cl  in
                                 let uu____5067 = cl repr  in
                                 let uu____5068 = cl return_repr  in
                                 let uu____5069 = cl bind_repr  in
                                 let uu____5070 =
                                   FStar_List.map
                                     (fun a  ->
                                        let uu___607_5078 = a  in
                                        let uu____5079 =
                                          let uu____5080 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_All.pipe_right uu____5080
                                            FStar_Pervasives_Native.snd
                                           in
                                        let uu____5105 =
                                          let uu____5106 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_All.pipe_right uu____5106
                                            FStar_Pervasives_Native.snd
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            (uu___607_5078.FStar_Syntax_Syntax.action_name);
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (uu___607_5078.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (uu___607_5078.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (uu___607_5078.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____5079;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____5105
                                        }) actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.is_layered =
                                     (uu___604_5054.FStar_Syntax_Syntax.is_layered);
                                   FStar_Syntax_Syntax.cattributes =
                                     (uu___604_5054.FStar_Syntax_Syntax.cattributes);
                                   FStar_Syntax_Syntax.mname =
                                     (uu___604_5054.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.univs =
                                     (uu___604_5054.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders =
                                     (uu___604_5054.FStar_Syntax_Syntax.binders);
                                   FStar_Syntax_Syntax.signature = uu____5055;
                                   FStar_Syntax_Syntax.ret_wp = uu____5056;
                                   FStar_Syntax_Syntax.bind_wp = uu____5057;
                                   FStar_Syntax_Syntax.stronger = uu____5058;
                                   FStar_Syntax_Syntax.match_wps = uu____5059;
                                   FStar_Syntax_Syntax.trivial = uu____5064;
                                   FStar_Syntax_Syntax.repr = uu____5067;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____5068;
                                   FStar_Syntax_Syntax.bind_repr = uu____5069;
                                   FStar_Syntax_Syntax.stronger_repr =
                                     FStar_Pervasives_Native.None;
                                   FStar_Syntax_Syntax.actions = uu____5070;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (uu___604_5054.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               ((let uu____5132 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____5132
                                 then
                                   let uu____5137 =
                                     FStar_Syntax_Print.eff_decl_to_string
                                       false ed3
                                      in
                                   FStar_Util.print1
                                     "Typechecked effect declaration:\n\t%s\n"
                                     uu____5137
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
      let uu____5164 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature)
         in
      match uu____5164 with
      | (effect_binders_un,signature_un) ->
          let uu____5185 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____5185 with
           | (effect_binders,env1,uu____5204) ->
               let uu____5205 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____5205 with
                | (signature,uu____5221) ->
                    let raise_error1 uu____5237 =
                      match uu____5237 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____5273  ->
                           match uu____5273 with
                           | (bv,qual) ->
                               let uu____5292 =
                                 let uu___632_5293 = bv  in
                                 let uu____5294 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___632_5293.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___632_5293.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____5294
                                 }  in
                               (uu____5292, qual)) effect_binders
                       in
                    let uu____5299 =
                      let uu____5306 =
                        let uu____5307 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____5307.FStar_Syntax_Syntax.n  in
                      match uu____5306 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____5317)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____5349 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____5299 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____5375 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____5375
                           then
                             let uu____5378 =
                               let uu____5381 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____5381  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____5378
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____5429 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____5429 with
                           | (t2,comp,uu____5442) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____5451 =
                           open_and_check env1 []
                             (FStar_Pervasives_Native.snd
                                ed.FStar_Syntax_Syntax.repr)
                            in
                         (match uu____5451 with
                          | (repr,_comp) ->
                              ((let uu____5479 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____5479
                                then
                                  let uu____5483 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____5483
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
                                let uu____5490 =
                                  recheck_debug "*" env1 wp_type  in
                                let wp_a =
                                  let uu____5493 =
                                    let uu____5494 =
                                      let uu____5495 =
                                        let uu____5512 =
                                          let uu____5523 =
                                            let uu____5532 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____5535 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____5532, uu____5535)  in
                                          [uu____5523]  in
                                        (wp_type, uu____5512)  in
                                      FStar_Syntax_Syntax.Tm_app uu____5495
                                       in
                                    mk1 uu____5494  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta] env1
                                    uu____5493
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____5583 =
                                      let uu____5590 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____5590)  in
                                    let uu____5596 =
                                      let uu____5605 =
                                        let uu____5612 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____5612
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____5605]  in
                                    uu____5583 :: uu____5596  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let uu____5649 =
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
                                  let uu____5715 = item  in
                                  match uu____5715 with
                                  | (u_item,item1) ->
                                      let uu____5730 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____5730 with
                                       | (item2,item_comp) ->
                                           ((let uu____5746 =
                                               let uu____5748 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____5748
                                                in
                                             if uu____5746
                                             then
                                               let uu____5751 =
                                                 let uu____5757 =
                                                   let uu____5759 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____5761 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____5759 uu____5761
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____5757)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____5751
                                             else ());
                                            (let uu____5767 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____5767 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let uu____5785 =
                                                   recheck_debug "*" env2
                                                     item_wp
                                                    in
                                                 let uu____5787 =
                                                   recheck_debug "_" env2
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab))))
                                   in
                                let uu____5789 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____5789 with
                                | (dmff_env1,uu____5815,bind_wp,bind_elab) ->
                                    let uu____5818 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____5818 with
                                     | (dmff_env2,uu____5844,return_wp,return_elab)
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
                                           let uu____5853 =
                                             let uu____5854 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____5854.FStar_Syntax_Syntax.n
                                              in
                                           match uu____5853 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____5912 =
                                                 let uu____5931 =
                                                   let uu____5936 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____5936
                                                    in
                                                 match uu____5931 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____6018 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____5912 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____6072 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____6072 [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____6095 =
                                                          let uu____6096 =
                                                            let uu____6113 =
                                                              let uu____6124
                                                                =
                                                                let uu____6133
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11)
                                                                   in
                                                                let uu____6138
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____6133,
                                                                  uu____6138)
                                                                 in
                                                              [uu____6124]
                                                               in
                                                            (wp_type,
                                                              uu____6113)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____6096
                                                           in
                                                        mk1 uu____6095  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Env.Beta]
                                                        env0 raw_wp_b1
                                                       in
                                                    let uu____6174 =
                                                      let uu____6183 =
                                                        let uu____6184 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____6184
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____6183
                                                       in
                                                    (match uu____6174 with
                                                     | (bs1,body2,what') ->
                                                         let fail1 uu____6207
                                                           =
                                                           let error_msg =
                                                             let uu____6210 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2
                                                                in
                                                             let uu____6212 =
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
                                                               uu____6210
                                                               uu____6212
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
                                                               ((let uu____6222
                                                                   =
                                                                   let uu____6224
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                   Prims.op_Negation
                                                                    uu____6224
                                                                    in
                                                                 if
                                                                   uu____6222
                                                                 then
                                                                   fail1 ()
                                                                 else ());
                                                                (let uu____6229
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
                                                                   uu____6229
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
                                                             let uu____6258 =
                                                               let uu____6263
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp
                                                                  in
                                                               let uu____6264
                                                                 =
                                                                 let uu____6265
                                                                   =
                                                                   let uu____6274
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                   (uu____6274,
                                                                    FStar_Pervasives_Native.None)
                                                                    in
                                                                 [uu____6265]
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____6263
                                                                 uu____6264
                                                                in
                                                             uu____6258
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange
                                                              in
                                                           let uu____6309 =
                                                             let uu____6310 =
                                                               let uu____6319
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp
                                                                  in
                                                               [uu____6319]
                                                                in
                                                             b11 ::
                                                               uu____6310
                                                              in
                                                           let uu____6344 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what
                                                              in
                                                           FStar_Syntax_Util.abs
                                                             uu____6309
                                                             uu____6344
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____6347 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let return_wp1 =
                                           let uu____6355 =
                                             let uu____6356 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____6356.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6355 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____6414 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____6414
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____6435 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let bind_wp1 =
                                           let uu____6443 =
                                             let uu____6444 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____6444.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6443 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_constant_at_level
                                                      Prims.int_one)
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let uu____6478 =
                                                 let uu____6479 =
                                                   let uu____6488 =
                                                     let uu____6495 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____6495
                                                      in
                                                   [uu____6488]  in
                                                 FStar_List.append uu____6479
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____6478 body what
                                           | uu____6514 ->
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
                                             (let uu____6544 =
                                                let uu____6545 =
                                                  let uu____6546 =
                                                    let uu____6563 =
                                                      let uu____6574 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____6574
                                                       in
                                                    (t, uu____6563)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____6546
                                                   in
                                                mk1 uu____6545  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____6544)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____6632 = f a2  in
                                               [uu____6632]
                                           | x::xs ->
                                               let uu____6643 =
                                                 apply_last1 f xs  in
                                               x :: uu____6643
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
                                           let uu____6677 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____6677 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____6707 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____6707
                                                 then
                                                   let uu____6710 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____6710
                                                 else ());
                                                (let uu____6715 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____6715))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____6724 =
                                                 let uu____6729 = mk_lid name
                                                    in
                                                 let uu____6730 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____6729 uu____6730
                                                  in
                                               (match uu____6724 with
                                                | (sigelt,fv) ->
                                                    ((let uu____6734 =
                                                        let uu____6737 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____6737
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____6734);
                                                     fv))
                                            in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp2 =
                                           register "return_wp" return_wp1
                                            in
                                         ((let uu____6791 =
                                             let uu____6794 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.PushOptions
                                                       (FStar_Pervasives_Native.Some
                                                          "--admit_smt_queries true")))
                                                in
                                             let uu____6797 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____6794 :: uu____6797  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____6791);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           (let uu____6849 =
                                              let uu____6852 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     FStar_Syntax_Syntax.PopOptions)
                                                 in
                                              let uu____6853 =
                                                FStar_ST.op_Bang sigelts  in
                                              uu____6852 :: uu____6853  in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____6849);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            (let uu____6905 =
                                               let uu____6908 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.PushOptions
                                                         (FStar_Pervasives_Native.Some
                                                            "--admit_smt_queries true")))
                                                  in
                                               let uu____6911 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____6908 :: uu____6911  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____6905);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             (let uu____6963 =
                                                let uu____6966 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       FStar_Syntax_Syntax.PopOptions)
                                                   in
                                                let uu____6967 =
                                                  FStar_ST.op_Bang sigelts
                                                   in
                                                uu____6966 :: uu____6967  in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____6963);
                                             (let uu____7016 =
                                                FStar_List.fold_left
                                                  (fun uu____7056  ->
                                                     fun action  ->
                                                       match uu____7056 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____7077 =
                                                             let uu____7084 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____7084
                                                               params_un
                                                              in
                                                           (match uu____7077
                                                            with
                                                            | (action_params,env',uu____7093)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____7119
                                                                     ->
                                                                    match uu____7119
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____7138
                                                                    =
                                                                    let uu___825_7139
                                                                    = bv  in
                                                                    let uu____7140
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___825_7139.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___825_7139.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____7140
                                                                    }  in
                                                                    (uu____7138,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____7146
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____7146
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
                                                                    uu____7185
                                                                    ->
                                                                    let uu____7186
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____7186
                                                                     in
                                                                    ((
                                                                    let uu____7190
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____7190
                                                                    then
                                                                    let uu____7195
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____7198
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____7201
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____7203
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____7195
                                                                    uu____7198
                                                                    uu____7201
                                                                    uu____7203
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
                                                                    let uu____7212
                                                                    =
                                                                    let uu____7215
                                                                    =
                                                                    let uu___847_7216
                                                                    = action
                                                                     in
                                                                    let uu____7217
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____7218
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___847_7216.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___847_7216.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___847_7216.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____7217;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____7218
                                                                    }  in
                                                                    uu____7215
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____7212))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____7016 with
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
                                                      let uu____7262 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____7269 =
                                                        let uu____7278 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____7278]  in
                                                      uu____7262 ::
                                                        uu____7269
                                                       in
                                                    let uu____7303 =
                                                      let uu____7306 =
                                                        let uu____7307 =
                                                          let uu____7308 =
                                                            let uu____7325 =
                                                              let uu____7336
                                                                =
                                                                let uu____7345
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____7348
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____7345,
                                                                  uu____7348)
                                                                 in
                                                              [uu____7336]
                                                               in
                                                            (repr,
                                                              uu____7325)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____7308
                                                           in
                                                        mk1 uu____7307  in
                                                      let uu____7384 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____7306
                                                        uu____7384
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____7303
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let uu____7385 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr2 =
                                                    register "repr" repr1  in
                                                  let uu____7389 =
                                                    let uu____7398 =
                                                      let uu____7399 =
                                                        let uu____7402 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____7402
                                                         in
                                                      uu____7399.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____7398 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____7416)
                                                        ->
                                                        let uu____7453 =
                                                          let uu____7474 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____7474
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____7542 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____7453
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____7607 =
                                                               let uu____7608
                                                                 =
                                                                 let uu____7611
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____7611
                                                                  in
                                                               uu____7608.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____7607
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____7644
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____7644
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____7659
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____7690
                                                                     ->
                                                                    match uu____7690
                                                                    with
                                                                    | 
                                                                    (bv,uu____7699)
                                                                    ->
                                                                    let uu____7704
                                                                    =
                                                                    let uu____7706
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____7706
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____7704
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____7659
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
                                                                    let uu____7798
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____7798
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____7808
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____7819
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____7819
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____7829
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____7832
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____7829,
                                                                    uu____7832)))
                                                              | uu____7847 ->
                                                                  let uu____7848
                                                                    =
                                                                    let uu____7854
                                                                    =
                                                                    let uu____7856
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____7856
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____7854)
                                                                     in
                                                                  raise_error1
                                                                    uu____7848))
                                                    | uu____7868 ->
                                                        let uu____7869 =
                                                          let uu____7875 =
                                                            let uu____7877 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type
                                                               in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____7877
                                                             in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____7875)
                                                           in
                                                        raise_error1
                                                          uu____7869
                                                     in
                                                  (match uu____7389 with
                                                   | (pre,post) ->
                                                       ((let uu____7910 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____7913 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____7916 =
                                                           register "wp"
                                                             wp_type
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___903_7919
                                                             = ed  in
                                                           let uu____7920 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____7921 =
                                                             let uu____7922 =
                                                               FStar_Syntax_Subst.close
                                                                 effect_binders1
                                                                 effect_signature
                                                                in
                                                             ([], uu____7922)
                                                              in
                                                           let uu____7929 =
                                                             let uu____7930 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____7930)
                                                              in
                                                           let uu____7937 =
                                                             let uu____7938 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____7938)
                                                              in
                                                           let uu____7945 =
                                                             let uu____7946 =
                                                               apply_close
                                                                 repr2
                                                                in
                                                             ([], uu____7946)
                                                              in
                                                           let uu____7953 =
                                                             let uu____7954 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____7954)
                                                              in
                                                           let uu____7961 =
                                                             let uu____7962 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____7962)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.is_layered
                                                               =
                                                               (uu___903_7919.FStar_Syntax_Syntax.is_layered);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___903_7919.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___903_7919.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___903_7919.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____7920;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____7921;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____7929;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____7937;
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___903_7919.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.match_wps
                                                               =
                                                               (uu___903_7919.FStar_Syntax_Syntax.match_wps);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___903_7919.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____7945;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____7953;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____7961;
                                                             FStar_Syntax_Syntax.stronger_repr
                                                               =
                                                               (uu___903_7919.FStar_Syntax_Syntax.stronger_repr);
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___903_7919.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____7969 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____7969
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____7987
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____7987
                                                               then
                                                                 let uu____7991
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____7991
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
                                                                    let uu____8011
                                                                    =
                                                                    let uu____8014
                                                                    =
                                                                    let uu____8015
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____8015)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____8014
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
                                                                    uu____8011;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____8022
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____8022
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____8025
                                                                 =
                                                                 let uu____8028
                                                                   =
                                                                   let uu____8031
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____8031
                                                                    in
                                                                 FStar_List.append
                                                                   uu____8028
                                                                   sigelts'
                                                                  in
                                                               (uu____8025,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____8072 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____8072 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____8107 = FStar_List.hd ses  in
            uu____8107.FStar_Syntax_Syntax.sigrng  in
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
           | uu____8112 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____8118,[],t,uu____8120,uu____8121);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____8123;
               FStar_Syntax_Syntax.sigattrs = uu____8124;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____8126,_t_top,_lex_t_top,_8160,uu____8129);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____8131;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____8132;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____8134,_t_cons,_lex_t_cons,_8168,uu____8137);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____8139;
                 FStar_Syntax_Syntax.sigattrs = uu____8140;_}::[]
               when
               ((_8160 = Prims.int_zero) && (_8168 = Prims.int_zero)) &&
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
                 let uu____8193 =
                   let uu____8200 =
                     let uu____8201 =
                       let uu____8208 =
                         let uu____8211 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____8211
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____8208, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____8201  in
                   FStar_Syntax_Syntax.mk uu____8200  in
                 uu____8193 FStar_Pervasives_Native.None r1  in
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
                   let uu____8226 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____8226
                    in
                 let hd1 =
                   let uu____8228 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____8228
                    in
                 let tl1 =
                   let uu____8230 =
                     let uu____8231 =
                       let uu____8238 =
                         let uu____8239 =
                           let uu____8246 =
                             let uu____8249 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____8249
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____8246, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____8239  in
                       FStar_Syntax_Syntax.mk uu____8238  in
                     uu____8231 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____8230
                    in
                 let res =
                   let uu____8255 =
                     let uu____8262 =
                       let uu____8263 =
                         let uu____8270 =
                           let uu____8273 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____8273
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____8270,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____8263  in
                     FStar_Syntax_Syntax.mk uu____8262  in
                   uu____8255 FStar_Pervasives_Native.None r2  in
                 let uu____8276 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____8276
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
               let uu____8315 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____8315;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____8320 ->
               let err_msg =
                 let uu____8325 =
                   let uu____8327 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____8327  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____8325
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
    fun uu____8352  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____8352 with
          | (uvs,t) ->
              let uu____8365 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____8365 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____8377 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____8377 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____8395 =
                        let uu____8398 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____8398
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____8395)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____8421 =
          let uu____8422 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____8422 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____8421 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____8447 =
          let uu____8448 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____8448 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____8447 r
  
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
          (let uu____8497 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____8497
           then
             let uu____8500 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____8500
           else ());
          (let uu____8505 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____8505 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____8536 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____8536 FStar_List.flatten  in
               ((let uu____8550 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____8553 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____8553)
                    in
                 if uu____8550
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
                           let uu____8569 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____8579,uu____8580,uu____8581,uu____8582,uu____8583)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____8592 -> failwith "Impossible!"  in
                           match uu____8569 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Inductive type "
                                      (Prims.op_Hat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____8611 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____8621,uu____8622,ty_lid,uu____8624,uu____8625)
                               -> (data_lid, ty_lid)
                           | uu____8632 -> failwith "Impossible"  in
                         match uu____8611 with
                         | (data_lid,ty_lid) ->
                             let uu____8640 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____8643 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____8643)
                                in
                             if uu____8640
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Exception "
                                      (Prims.op_Hat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____8657 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____8662,uu____8663,uu____8664,uu____8665,uu____8666)
                         -> lid
                     | uu____8675 -> failwith "Impossible"  in
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
                   let uu____8693 =
                     (((FStar_List.length tcs) = Prims.int_zero) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____8693
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
          let pop1 uu____8768 =
            let uu____8769 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___1081_8779  ->
               match () with
               | () ->
                   let uu____8786 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____8786 (fun r  -> pop1 (); r)) ()
          with | uu___1080_8817 -> (pop1 (); FStar_Exn.raise uu___1080_8817)
  
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
      | uu____9133 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____9191 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____9191 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____9216 .
    'Auu____9216 FStar_Pervasives_Native.option -> 'Auu____9216 Prims.list
  =
  fun uu___0_9225  ->
    match uu___0_9225 with
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
            let uu____9305 = collect1 tl1  in
            (match uu____9305 with
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
        | ((e,n1)::uu____9543,[]) ->
            FStar_Pervasives_Native.Some (e, n1, Prims.int_zero)
        | ([],(e,n1)::uu____9599) ->
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
          let uu____9809 =
            let uu____9811 = FStar_Options.ide ()  in
            Prims.op_Negation uu____9811  in
          if uu____9809
          then
            let uu____9814 =
              let uu____9819 = FStar_TypeChecker_Env.dsenv env  in
              let uu____9820 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____9819 uu____9820  in
            (match uu____9814 with
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
                              let uu____9853 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____9854 =
                                let uu____9860 =
                                  let uu____9862 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____9864 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____9862 uu____9864
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____9860)
                                 in
                              FStar_Errors.log_issue uu____9853 uu____9854
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____9871 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____9872 =
                                   let uu____9878 =
                                     let uu____9880 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____9880
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____9878)
                                    in
                                 FStar_Errors.log_issue uu____9871 uu____9872)
                              else ())
                         else ())))
          else ()
      | uu____9890 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____9935 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____9963 ->
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
             let uu____10023 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____10023
             then
               let ses1 =
                 let uu____10031 =
                   let uu____10032 =
                     let uu____10033 =
                       tc_inductive
                         (let uu___1213_10042 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1213_10042.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1213_10042.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1213_10042.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1213_10042.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1213_10042.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1213_10042.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1213_10042.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1213_10042.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1213_10042.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1213_10042.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1213_10042.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1213_10042.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1213_10042.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1213_10042.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1213_10042.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1213_10042.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1213_10042.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1213_10042.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1213_10042.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1213_10042.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1213_10042.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___1213_10042.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1213_10042.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1213_10042.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1213_10042.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1213_10042.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1213_10042.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1213_10042.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1213_10042.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1213_10042.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1213_10042.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1213_10042.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1213_10042.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1213_10042.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1213_10042.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1213_10042.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1213_10042.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1213_10042.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1213_10042.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1213_10042.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1213_10042.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1213_10042.FStar_TypeChecker_Env.strict_args_tab)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____10033
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____10032
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____10031
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____10056 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____10056
                 then
                   let uu____10061 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1217_10065 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1217_10065.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1217_10065.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1217_10065.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1217_10065.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____10061
                 else ());
                ses1)
             else ses  in
           let uu____10075 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____10075 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___1224_10099 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1224_10099.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1224_10099.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1224_10099.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1224_10099.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____10111 = cps_and_elaborate env ne  in
           (match uu____10111 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___1238_10150 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1238_10150.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1238_10150.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1238_10150.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1238_10150.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___1241_10152 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1241_10152.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1241_10152.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1241_10152.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1241_10152.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses), env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           ((let uu____10159 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "LayeredEffects")
                in
             if uu____10159
             then
               let uu____10164 = FStar_Syntax_Print.sigelt_to_string se  in
               FStar_Util.print1
                 "Starting to typecheck layered effect:\n%s\n" uu____10164
             else ());
            (let tc_fun =
               if ne.FStar_Syntax_Syntax.is_layered
               then tc_layered_eff_decl
               else tc_eff_decl  in
             let ne1 =
               let uu____10188 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env)
                  in
               if uu____10188
               then
                 let ne1 =
                   let uu____10192 =
                     let uu____10193 =
                       let uu____10194 =
                         tc_fun
                           (let uu___1251_10197 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1251_10197.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1251_10197.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1251_10197.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1251_10197.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1251_10197.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1251_10197.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1251_10197.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1251_10197.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1251_10197.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1251_10197.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1251_10197.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1251_10197.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1251_10197.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1251_10197.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1251_10197.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1251_10197.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1251_10197.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1251_10197.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1251_10197.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1251_10197.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1251_10197.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 = true;
                              FStar_TypeChecker_Env.failhard =
                                (uu___1251_10197.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1251_10197.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1251_10197.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1251_10197.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1251_10197.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1251_10197.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1251_10197.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1251_10197.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1251_10197.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1251_10197.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1251_10197.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1251_10197.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1251_10197.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1251_10197.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1251_10197.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1251_10197.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1251_10197.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1251_10197.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1251_10197.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1251_10197.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1251_10197.FStar_TypeChecker_Env.strict_args_tab)
                            }) ne
                          in
                       FStar_All.pipe_right uu____10194
                         (fun ne1  ->
                            let uu___1254_10203 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_new_effect ne1);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___1254_10203.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___1254_10203.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___1254_10203.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___1254_10203.FStar_Syntax_Syntax.sigattrs)
                            })
                        in
                     FStar_All.pipe_right uu____10193
                       (FStar_TypeChecker_Normalize.elim_uvars env)
                      in
                   FStar_All.pipe_right uu____10192
                     FStar_Syntax_Util.eff_decl_of_new_effect
                    in
                 ((let uu____10205 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "TwoPhases")
                      in
                   if uu____10205
                   then
                     let uu____10210 =
                       FStar_Syntax_Print.sigelt_to_string
                         (let uu___1258_10214 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1258_10214.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1258_10214.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1258_10214.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1258_10214.FStar_Syntax_Syntax.sigattrs)
                          })
                        in
                     FStar_Util.print1 "Effect decl after phase 1: %s\n"
                       uu____10210
                   else ());
                  ne1)
               else ne  in
             let ne2 = tc_fun env ne1  in
             let se1 =
               let uu___1263_10222 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_new_effect ne2);
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1263_10222.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1263_10222.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1263_10222.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1263_10222.FStar_Syntax_Syntax.sigattrs)
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
           let uu____10230 =
             let uu____10237 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____10237
              in
           (match uu____10230 with
            | (a,wp_a_src) ->
                let uu____10254 =
                  let uu____10261 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____10261
                   in
                (match uu____10254 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____10279 =
                         let uu____10282 =
                           let uu____10283 =
                             let uu____10290 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____10290)  in
                           FStar_Syntax_Syntax.NT uu____10283  in
                         [uu____10282]  in
                       FStar_Syntax_Subst.subst uu____10279 wp_b_tgt  in
                     let expected_k =
                       let uu____10298 =
                         let uu____10307 = FStar_Syntax_Syntax.mk_binder a
                            in
                         let uu____10314 =
                           let uu____10323 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____10323]  in
                         uu____10307 :: uu____10314  in
                       let uu____10348 =
                         FStar_Syntax_Syntax.mk_Total wp_a_tgt  in
                       FStar_Syntax_Util.arrow uu____10298 uu____10348  in
                     let repr_type eff_name a1 wp =
                       (let uu____10370 =
                          let uu____10372 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name
                             in
                          Prims.op_Negation uu____10372  in
                        if uu____10370
                        then
                          let uu____10375 =
                            let uu____10381 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____10381)
                             in
                          let uu____10385 =
                            FStar_TypeChecker_Env.get_range env  in
                          FStar_Errors.raise_error uu____10375 uu____10385
                        else ());
                       (let uu____10388 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name
                           in
                        match uu____10388 with
                        | FStar_Pervasives_Native.None  ->
                            failwith
                              "internal error: reifiable effect has no decl?"
                        | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                            let repr =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [FStar_Syntax_Syntax.U_unknown] env ed
                                ed.FStar_Syntax_Syntax.repr
                               in
                            let uu____10421 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____10422 =
                              let uu____10429 =
                                let uu____10430 =
                                  let uu____10447 =
                                    let uu____10458 =
                                      FStar_Syntax_Syntax.as_arg a1  in
                                    let uu____10467 =
                                      let uu____10478 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____10478]  in
                                    uu____10458 :: uu____10467  in
                                  (repr, uu____10447)  in
                                FStar_Syntax_Syntax.Tm_app uu____10430  in
                              FStar_Syntax_Syntax.mk uu____10429  in
                            uu____10422 FStar_Pervasives_Native.None
                              uu____10421)
                        in
                     let uu____10523 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____10696 =
                             if (FStar_List.length uvs) > Prims.int_zero
                             then
                               let uu____10707 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____10707 with
                               | (usubst,uvs1) ->
                                   let uu____10730 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____10731 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____10730, uu____10731)
                             else (env, lift_wp)  in
                           (match uu____10696 with
                            | (env1,lift_wp1) ->
                                let lift_wp2 =
                                  if (FStar_List.length uvs) = Prims.int_zero
                                  then check_and_gen env1 lift_wp1 expected_k
                                  else
                                    (let lift_wp2 =
                                       tc_check_trivial_guard env1 lift_wp1
                                         expected_k
                                        in
                                     let uu____10781 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____10781))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____10852 =
                             if (FStar_List.length what) > Prims.int_zero
                             then
                               let uu____10867 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____10867 with
                               | (usubst,uvs) ->
                                   let uu____10892 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____10892)
                             else ([], lift)  in
                           (match uu____10852 with
                            | (uvs,lift1) ->
                                ((let uu____10928 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____10928
                                  then
                                    let uu____10932 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____10932
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____10938 =
                                    let uu____10945 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____10945 lift1
                                     in
                                  match uu____10938 with
                                  | (lift2,comp,uu____10970) ->
                                      let uu____10971 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____10971 with
                                       | (uu____11000,lift_wp,lift_elab) ->
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
                                             let uu____11032 =
                                               let uu____11043 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____11043
                                                in
                                             let uu____11060 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____11032, uu____11060)
                                           else
                                             (let uu____11089 =
                                                let uu____11100 =
                                                  let uu____11109 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____11109)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____11100
                                                 in
                                              let uu____11124 =
                                                let uu____11133 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____11133)  in
                                              (uu____11089, uu____11124))))))
                        in
                     (match uu____10523 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___1339_11207 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1339_11207.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1339_11207.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1339_11207.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1339_11207.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1339_11207.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1339_11207.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1339_11207.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1339_11207.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1339_11207.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1339_11207.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1339_11207.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1339_11207.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1339_11207.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1339_11207.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1339_11207.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1339_11207.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1339_11207.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1339_11207.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1339_11207.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1339_11207.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1339_11207.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1339_11207.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1339_11207.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1339_11207.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1339_11207.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1339_11207.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1339_11207.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1339_11207.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1339_11207.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1339_11207.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1339_11207.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1339_11207.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1339_11207.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1339_11207.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1339_11207.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1339_11207.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1339_11207.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1339_11207.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1339_11207.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1339_11207.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1339_11207.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1339_11207.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1339_11207.FStar_TypeChecker_Env.strict_args_tab)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____11264 =
                                  let uu____11269 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____11269 with
                                  | (usubst,uvs1) ->
                                      let uu____11292 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____11293 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____11292, uu____11293)
                                   in
                                (match uu____11264 with
                                 | (env2,lift2) ->
                                     let uu____11306 =
                                       let uu____11313 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____11313
                                        in
                                     (match uu____11306 with
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
                                              let uu____11347 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____11348 =
                                                let uu____11355 =
                                                  let uu____11356 =
                                                    let uu____11373 =
                                                      let uu____11384 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____11393 =
                                                        let uu____11404 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____11404]  in
                                                      uu____11384 ::
                                                        uu____11393
                                                       in
                                                    (lift_wp1, uu____11373)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____11356
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____11355
                                                 in
                                              uu____11348
                                                FStar_Pervasives_Native.None
                                                uu____11347
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____11452 =
                                              let uu____11461 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____11468 =
                                                let uu____11477 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____11484 =
                                                  let uu____11493 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____11493]  in
                                                uu____11477 :: uu____11484
                                                 in
                                              uu____11461 :: uu____11468  in
                                            let uu____11524 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____11452 uu____11524
                                             in
                                          let uu____11527 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____11527 with
                                           | (expected_k2,uu____11545,uu____11546)
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
                                                    let uu____11570 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____11570))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____11586 =
                              let uu____11588 =
                                let uu____11590 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____11590
                                  FStar_List.length
                                 in
                              uu____11588 <> Prims.int_one  in
                            if uu____11586
                            then
                              let uu____11612 =
                                let uu____11618 =
                                  let uu____11620 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____11622 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____11624 =
                                    let uu____11626 =
                                      let uu____11628 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____11628
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____11626
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____11620 uu____11622 uu____11624
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____11618)
                                 in
                              FStar_Errors.raise_error uu____11612 r
                            else ());
                           (let uu____11655 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____11666 =
                                   let uu____11668 =
                                     let uu____11671 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____11671
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____11668
                                     FStar_List.length
                                    in
                                 uu____11666 <> Prims.int_one)
                               in
                            if uu____11655
                            then
                              let uu____11725 =
                                let uu____11731 =
                                  let uu____11733 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____11735 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____11737 =
                                    let uu____11739 =
                                      let uu____11741 =
                                        let uu____11744 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____11744
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____11741
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____11739
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____11733 uu____11735 uu____11737
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____11731)
                                 in
                              FStar_Errors.raise_error uu____11725 r
                            else ());
                           (let sub2 =
                              let uu___1376_11803 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___1376_11803.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___1376_11803.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___1379_11805 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___1379_11805.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___1379_11805.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___1379_11805.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___1379_11805.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let uu____11819 =
             if (FStar_List.length uvs) = Prims.int_zero
             then (env, uvs, tps, c)
             else
               (let uu____11847 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____11847 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____11878 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____11878 c  in
                    let uu____11887 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____11887, uvs1, tps1, c1))
              in
           (match uu____11819 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____11909 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____11909 with
                 | (tps2,c2) ->
                     let uu____11926 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____11926 with
                      | (tps3,env3,us) ->
                          let uu____11946 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____11946 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____11974)::uu____11975 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____11994 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____12002 =
                                   let uu____12004 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____12004  in
                                 if uu____12002
                                 then
                                   let uu____12007 =
                                     let uu____12013 =
                                       let uu____12015 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____12017 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____12015 uu____12017
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____12013)
                                      in
                                   FStar_Errors.raise_error uu____12007 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____12025 =
                                   let uu____12026 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____12026
                                    in
                                 match uu____12025 with
                                 | (uvs2,t) ->
                                     let uu____12057 =
                                       let uu____12062 =
                                         let uu____12075 =
                                           let uu____12076 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____12076.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____12075)  in
                                       match uu____12062 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____12091,c5)) -> ([], c5)
                                       | (uu____12133,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____12172 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____12057 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               Prims.int_one
                                           then
                                             (let uu____12206 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____12206 with
                                              | (uu____12211,t1) ->
                                                  let uu____12213 =
                                                    let uu____12219 =
                                                      let uu____12221 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____12223 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____12227 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____12221
                                                        uu____12223
                                                        uu____12227
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____12219)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____12213 r)
                                           else ();
                                           (let se1 =
                                              let uu___1449_12234 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___1449_12234.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___1449_12234.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___1449_12234.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___1449_12234.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____12241,uu____12242,uu____12243) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_12248  ->
                   match uu___1_12248 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____12251 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____12257,uu____12258) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_12267  ->
                   match uu___1_12267 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____12270 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____12281 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____12281
             then
               let uu____12284 =
                 let uu____12290 =
                   let uu____12292 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____12292
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____12290)
                  in
               FStar_Errors.raise_error uu____12284 r
             else ());
            (let uu____12298 =
               let uu____12307 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____12307
               then
                 let uu____12318 =
                   tc_declare_typ
                     (let uu___1473_12321 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1473_12321.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1473_12321.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1473_12321.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1473_12321.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1473_12321.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1473_12321.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1473_12321.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1473_12321.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1473_12321.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1473_12321.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1473_12321.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1473_12321.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1473_12321.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1473_12321.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1473_12321.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1473_12321.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1473_12321.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1473_12321.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1473_12321.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1473_12321.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1473_12321.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1473_12321.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1473_12321.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1473_12321.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1473_12321.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1473_12321.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1473_12321.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1473_12321.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1473_12321.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1473_12321.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1473_12321.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1473_12321.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1473_12321.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1473_12321.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1473_12321.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1473_12321.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1473_12321.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1473_12321.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1473_12321.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1473_12321.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___1473_12321.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___1473_12321.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1473_12321.FStar_TypeChecker_Env.strict_args_tab)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____12318 with
                 | (uvs1,t1) ->
                     ((let uu____12346 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____12346
                       then
                         let uu____12351 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____12353 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____12351 uu____12353
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____12298 with
             | (uvs1,t1) ->
                 let uu____12388 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____12388 with
                  | (uvs2,t2) ->
                      ([(let uu___1486_12418 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1486_12418.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1486_12418.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1486_12418.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1486_12418.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____12423 =
             let uu____12432 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____12432
             then
               let uu____12443 =
                 tc_assume
                   (let uu___1495_12446 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1495_12446.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1495_12446.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1495_12446.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1495_12446.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1495_12446.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1495_12446.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1495_12446.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1495_12446.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1495_12446.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1495_12446.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1495_12446.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1495_12446.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1495_12446.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1495_12446.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1495_12446.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1495_12446.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1495_12446.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1495_12446.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1495_12446.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1495_12446.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1495_12446.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___1495_12446.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1495_12446.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1495_12446.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1495_12446.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1495_12446.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1495_12446.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1495_12446.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1495_12446.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1495_12446.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1495_12446.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1495_12446.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1495_12446.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1495_12446.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1495_12446.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1495_12446.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1495_12446.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1495_12446.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1495_12446.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1495_12446.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1495_12446.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1495_12446.FStar_TypeChecker_Env.strict_args_tab)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____12443 with
               | (uvs1,t1) ->
                   ((let uu____12472 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____12472
                     then
                       let uu____12477 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12479 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____12477
                         uu____12479
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____12423 with
            | (uvs1,t1) ->
                let uu____12514 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____12514 with
                 | (uvs2,t2) ->
                     ([(let uu___1508_12544 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1508_12544.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1508_12544.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1508_12544.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1508_12544.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____12548 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____12548 with
            | (e1,c,g1) ->
                let uu____12568 =
                  let uu____12575 =
                    let uu____12578 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____12578  in
                  let uu____12579 =
                    let uu____12584 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____12584)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____12575 uu____12579
                   in
                (match uu____12568 with
                 | (e2,uu____12596,g) ->
                     ((let uu____12599 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____12599);
                      (let se1 =
                         let uu___1523_12601 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1523_12601.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1523_12601.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1523_12601.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1523_12601.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____12613 = FStar_Options.debug_any ()  in
             if uu____12613
             then
               let uu____12616 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____12618 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____12616
                 uu____12618
             else ());
            (let uu____12623 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____12623 with
             | (t1,uu____12641,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____12655 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____12655 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____12658 =
                              let uu____12664 =
                                let uu____12666 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____12668 =
                                  let uu____12670 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____12670
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____12666 uu____12668
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____12664)
                               in
                            FStar_Errors.raise_error uu____12658 r
                        | uu____12682 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___1544_12687 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1544_12687.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1544_12687.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1544_12687.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1544_12687.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1544_12687.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1544_12687.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1544_12687.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1544_12687.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1544_12687.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1544_12687.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1544_12687.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1544_12687.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1544_12687.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1544_12687.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1544_12687.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1544_12687.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1544_12687.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1544_12687.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1544_12687.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1544_12687.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___1544_12687.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1544_12687.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1544_12687.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1544_12687.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1544_12687.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1544_12687.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1544_12687.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1544_12687.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1544_12687.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1544_12687.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1544_12687.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1544_12687.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1544_12687.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1544_12687.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1544_12687.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1544_12687.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1544_12687.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1544_12687.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1544_12687.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1544_12687.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1544_12687.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___1544_12687.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1544_12687.FStar_TypeChecker_Env.strict_args_tab)
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
                 let uu____12755 =
                   let uu____12757 =
                     let uu____12766 = drop_logic val_q  in
                     let uu____12769 = drop_logic q'  in
                     (uu____12766, uu____12769)  in
                   match uu____12757 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____12755
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____12796 =
                      let uu____12802 =
                        let uu____12804 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____12806 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____12808 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____12804 uu____12806 uu____12808
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____12802)
                       in
                    FStar_Errors.raise_error uu____12796 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____12845 =
                   let uu____12846 = FStar_Syntax_Subst.compress def  in
                   uu____12846.FStar_Syntax_Syntax.n  in
                 match uu____12845 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____12858,uu____12859) -> binders
                 | uu____12884 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____12896;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____13001) -> val_bs1
                     | (uu____13032,[]) -> val_bs1
                     | ((body_bv,uu____13064)::bt,(val_bv,aqual)::vt) ->
                         let uu____13121 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____13145) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___1613_13159 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___1615_13162 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___1615_13162.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___1613_13159.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1613_13159.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____13121
                      in
                   let uu____13169 =
                     let uu____13176 =
                       let uu____13177 =
                         let uu____13192 = rename_binders1 def_bs val_bs  in
                         (uu____13192, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____13177  in
                     FStar_Syntax_Syntax.mk uu____13176  in
                   uu____13169 FStar_Pervasives_Native.None r1
               | uu____13211 -> typ1  in
             let uu___1621_13212 = lb  in
             let uu____13213 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___1621_13212.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1621_13212.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____13213;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1621_13212.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___1621_13212.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1621_13212.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1621_13212.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____13216 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____13271  ->
                     fun lb  ->
                       match uu____13271 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____13317 =
                             let uu____13329 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____13329 with
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
                                   | uu____13409 ->
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
                                  (let uu____13456 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____13456, quals_opt1)))
                              in
                           (match uu____13317 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____13216 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____13560 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___2_13566  ->
                                match uu___2_13566 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____13571 -> false))
                         in
                      if uu____13560
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____13584 =
                    let uu____13591 =
                      let uu____13592 =
                        let uu____13606 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____13606)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____13592  in
                    FStar_Syntax_Syntax.mk uu____13591  in
                  uu____13584 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___1664_13625 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1664_13625.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1664_13625.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1664_13625.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1664_13625.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1664_13625.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1664_13625.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1664_13625.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1664_13625.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1664_13625.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1664_13625.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1664_13625.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1664_13625.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1664_13625.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1664_13625.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1664_13625.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1664_13625.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1664_13625.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1664_13625.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1664_13625.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1664_13625.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1664_13625.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1664_13625.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1664_13625.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1664_13625.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1664_13625.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1664_13625.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1664_13625.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1664_13625.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1664_13625.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1664_13625.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1664_13625.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1664_13625.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1664_13625.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1664_13625.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1664_13625.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1664_13625.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1664_13625.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1664_13625.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1664_13625.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1664_13625.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1664_13625.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___1664_13625.FStar_TypeChecker_Env.strict_args_tab)
                  }  in
                let e1 =
                  let uu____13628 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____13628
                  then
                    let drop_lbtyp e_lax =
                      let uu____13637 =
                        let uu____13638 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____13638.FStar_Syntax_Syntax.n  in
                      match uu____13637 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____13660 =
                              let uu____13661 = FStar_Syntax_Subst.compress e
                                 in
                              uu____13661.FStar_Syntax_Syntax.n  in
                            match uu____13660 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____13665,lb1::[]),uu____13667) ->
                                let uu____13683 =
                                  let uu____13684 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____13684.FStar_Syntax_Syntax.n  in
                                (match uu____13683 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____13689 -> false)
                            | uu____13691 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___1689_13695 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___1691_13710 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___1691_13710.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___1691_13710.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___1691_13710.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___1691_13710.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___1691_13710.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___1691_13710.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___1689_13695.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___1689_13695.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____13713 -> e_lax  in
                    let uu____13714 =
                      FStar_Util.record_time
                        (fun uu____13722  ->
                           let uu____13723 =
                             let uu____13724 =
                               let uu____13725 =
                                 FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                   (let uu___1695_13734 = env'  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___1695_13734.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___1695_13734.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___1695_13734.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___1695_13734.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___1695_13734.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___1695_13734.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___1695_13734.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___1695_13734.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___1695_13734.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___1695_13734.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___1695_13734.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___1695_13734.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___1695_13734.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___1695_13734.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___1695_13734.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___1695_13734.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___1695_13734.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___1695_13734.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___1695_13734.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___1695_13734.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___1695_13734.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___1695_13734.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___1695_13734.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___1695_13734.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___1695_13734.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___1695_13734.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___1695_13734.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___1695_13734.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___1695_13734.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___1695_13734.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___1695_13734.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___1695_13734.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___1695_13734.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___1695_13734.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___1695_13734.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___1695_13734.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___1695_13734.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___1695_13734.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___1695_13734.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___1695_13734.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___1695_13734.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___1695_13734.FStar_TypeChecker_Env.strict_args_tab)
                                    }) e
                                  in
                               FStar_All.pipe_right uu____13725
                                 (fun uu____13747  ->
                                    match uu____13747 with
                                    | (e1,uu____13755,uu____13756) -> e1)
                                in
                             FStar_All.pipe_right uu____13724
                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                  env')
                              in
                           FStar_All.pipe_right uu____13723 drop_lbtyp)
                       in
                    match uu____13714 with
                    | (e1,ms) ->
                        ((let uu____13762 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TwoPhases")
                             in
                          if uu____13762
                          then
                            let uu____13767 =
                              FStar_Syntax_Print.term_to_string e1  in
                            FStar_Util.print1
                              "Let binding after phase 1: %s\n" uu____13767
                          else ());
                         (let uu____13773 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TCDeclTime")
                             in
                          if uu____13773
                          then
                            let uu____13778 = FStar_Util.string_of_int ms  in
                            FStar_Util.print1
                              "Let binding elaborated (phase 1) in %s milliseconds\n"
                              uu____13778
                          else ());
                         e1)
                  else e  in
                let uu____13785 =
                  let uu____13794 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____13794 with
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
                (match uu____13785 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___1725_13899 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___1725_13899.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1725_13899.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1725_13899.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1725_13899.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___1732_13912 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1732_13912.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1732_13912.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___1732_13912.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___1732_13912.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1732_13912.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1732_13912.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____13913 =
                       FStar_Util.record_time
                         (fun uu____13932  ->
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              env' e1)
                        in
                     (match uu____13913 with
                      | (r1,ms) ->
                          ((let uu____13960 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TCDeclTime")
                               in
                            if uu____13960
                            then
                              let uu____13965 = FStar_Util.string_of_int ms
                                 in
                              FStar_Util.print1
                                "Let binding typechecked in phase 2 in %s milliseconds\n"
                                uu____13965
                            else ());
                           (let uu____13970 =
                              match r1 with
                              | ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                                   FStar_Syntax_Syntax.pos = uu____13995;
                                   FStar_Syntax_Syntax.vars = uu____13996;_},uu____13997,g)
                                  when FStar_TypeChecker_Env.is_trivial g ->
                                  let lbs2 =
                                    let uu____14027 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.snd lbs1)
                                        (FStar_List.map rename_parameters)
                                       in
                                    ((FStar_Pervasives_Native.fst lbs1),
                                      uu____14027)
                                     in
                                  let lbs3 =
                                    let uu____14051 =
                                      match post_tau with
                                      | FStar_Pervasives_Native.Some tau ->
                                          FStar_List.map (postprocess_lb tau)
                                            (FStar_Pervasives_Native.snd lbs2)
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.snd lbs2
                                       in
                                    ((FStar_Pervasives_Native.fst lbs2),
                                      uu____14051)
                                     in
                                  let quals1 =
                                    match e2.FStar_Syntax_Syntax.n with
                                    | FStar_Syntax_Syntax.Tm_meta
                                        (uu____14074,FStar_Syntax_Syntax.Meta_desugared
                                         (FStar_Syntax_Syntax.Masked_effect
                                         ))
                                        ->
                                        FStar_Syntax_Syntax.HasMaskedEffect
                                        :: quals
                                    | uu____14079 -> quals  in
                                  ((let uu___1762_14088 = se1  in
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_let
                                           (lbs3, lids));
                                      FStar_Syntax_Syntax.sigrng =
                                        (uu___1762_14088.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals = quals1;
                                      FStar_Syntax_Syntax.sigmeta =
                                        (uu___1762_14088.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (uu___1762_14088.FStar_Syntax_Syntax.sigattrs)
                                    }), lbs3)
                              | uu____14091 ->
                                  failwith
                                    "impossible (typechecking should preserve Tm_let)"
                               in
                            match uu____13970 with
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
                                 (let uu____14147 = log env1  in
                                  if uu____14147
                                  then
                                    let uu____14150 =
                                      let uu____14152 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.snd lbs1)
                                          (FStar_List.map
                                             (fun lb  ->
                                                let should_log =
                                                  let uu____14172 =
                                                    let uu____14181 =
                                                      let uu____14182 =
                                                        let uu____14185 =
                                                          FStar_Util.right
                                                            lb.FStar_Syntax_Syntax.lbname
                                                           in
                                                        uu____14185.FStar_Syntax_Syntax.fv_name
                                                         in
                                                      uu____14182.FStar_Syntax_Syntax.v
                                                       in
                                                    FStar_TypeChecker_Env.try_lookup_val_decl
                                                      env1 uu____14181
                                                     in
                                                  match uu____14172 with
                                                  | FStar_Pervasives_Native.None
                                                       -> true
                                                  | uu____14194 -> false  in
                                                if should_log
                                                then
                                                  let uu____14206 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  let uu____14208 =
                                                    FStar_Syntax_Print.term_to_string
                                                      lb.FStar_Syntax_Syntax.lbtyp
                                                     in
                                                  FStar_Util.format2
                                                    "let %s : %s" uu____14206
                                                    uu____14208
                                                else ""))
                                         in
                                      FStar_All.pipe_right uu____14152
                                        (FStar_String.concat "\n")
                                       in
                                    FStar_Util.print1 "%s\n" uu____14150
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
      (let uu____14260 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____14260
       then
         let uu____14263 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____14263
       else ());
      (let uu____14268 = get_fail_se se  in
       match uu____14268 with
       | FStar_Pervasives_Native.Some (uu____14289,false ) when
           let uu____14306 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____14306 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___1793_14332 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___1793_14332.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___1793_14332.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___1793_14332.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___1793_14332.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___1793_14332.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___1793_14332.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___1793_14332.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___1793_14332.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___1793_14332.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___1793_14332.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___1793_14332.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___1793_14332.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___1793_14332.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___1793_14332.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___1793_14332.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___1793_14332.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___1793_14332.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___1793_14332.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___1793_14332.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___1793_14332.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___1793_14332.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___1793_14332.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___1793_14332.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___1793_14332.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___1793_14332.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___1793_14332.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___1793_14332.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___1793_14332.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___1793_14332.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___1793_14332.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___1793_14332.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___1793_14332.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___1793_14332.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___1793_14332.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___1793_14332.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___1793_14332.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___1793_14332.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___1793_14332.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___1793_14332.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___1793_14332.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___1793_14332.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___1793_14332.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___1793_14332.FStar_TypeChecker_Env.strict_args_tab)
               }
             else env1  in
           ((let uu____14337 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____14337
             then
               let uu____14340 =
                 let uu____14342 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____14342
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____14340
             else ());
            (let uu____14356 =
               FStar_Errors.catch_errors
                 (fun uu____14386  ->
                    FStar_Options.with_saved_options
                      (fun uu____14398  -> tc_decl' env' se))
                in
             match uu____14356 with
             | (errs,uu____14410) ->
                 ((let uu____14440 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____14440
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____14475 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____14475  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____14487 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____14498 =
                            let uu____14508 = check_multi_eq errnos1 actual
                               in
                            match uu____14508 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- Prims.int_one), (~- Prims.int_one),
                                  (~- Prims.int_one))
                             in
                          (match uu____14498 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____14573 =
                                   let uu____14579 =
                                     let uu____14581 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____14584 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____14587 =
                                       FStar_Util.string_of_int e  in
                                     let uu____14589 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____14591 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____14581 uu____14584 uu____14587
                                       uu____14589 uu____14591
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____14579)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____14573)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____14618 .
    'Auu____14618 ->
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
               (fun uu___3_14661  ->
                  match uu___3_14661 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____14664 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____14675) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____14683 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____14693 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____14698 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____14714 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____14740 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14766) ->
            let uu____14775 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____14775
            then
              let for_export_bundle se1 uu____14812 =
                match uu____14812 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____14851,uu____14852) ->
                         let dec =
                           let uu___1869_14862 = se1  in
                           let uu____14863 =
                             let uu____14864 =
                               let uu____14871 =
                                 let uu____14872 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____14872  in
                               (l, us, uu____14871)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____14864
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____14863;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1869_14862.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1869_14862.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1869_14862.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____14882,uu____14883,uu____14884) ->
                         let dec =
                           let uu___1880_14892 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1880_14892.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1880_14892.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1880_14892.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____14897 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____14920,uu____14921,uu____14922) ->
            let uu____14923 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____14923 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____14947 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____14947
            then
              ([(let uu___1896_14966 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___1896_14966.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___1896_14966.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___1896_14966.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____14969 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_14975  ->
                         match uu___4_14975 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____14978 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____14984 ->
                             true
                         | uu____14986 -> false))
                  in
               if uu____14969 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____15007 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____15012 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15017 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____15022 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15027 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____15045) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____15059 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____15059
            then ([], hidden)
            else
              (let dec =
                 let uu____15080 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____15080;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____15091 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____15091
            then
              let uu____15102 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1933_15116 = se  in
                        let uu____15117 =
                          let uu____15118 =
                            let uu____15125 =
                              let uu____15126 =
                                let uu____15129 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____15129.FStar_Syntax_Syntax.fv_name  in
                              uu____15126.FStar_Syntax_Syntax.v  in
                            (uu____15125, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____15118  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____15117;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1933_15116.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1933_15116.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1933_15116.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____15102, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____15152 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____15152
       then
         let uu____15155 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____15155
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____15160 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____15178 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
           uu____15195) ->
           let env1 =
             let uu___1954_15200 = env  in
             let uu____15201 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1954_15200.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1954_15200.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1954_15200.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1954_15200.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1954_15200.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1954_15200.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1954_15200.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1954_15200.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1954_15200.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1954_15200.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1954_15200.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1954_15200.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1954_15200.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1954_15200.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1954_15200.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1954_15200.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1954_15200.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1954_15200.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1954_15200.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1954_15200.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1954_15200.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1954_15200.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1954_15200.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1954_15200.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1954_15200.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1954_15200.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1954_15200.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1954_15200.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1954_15200.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1954_15200.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1954_15200.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1954_15200.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1954_15200.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1954_15200.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____15201;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1954_15200.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1954_15200.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1954_15200.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1954_15200.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1954_15200.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1954_15200.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1954_15200.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1954_15200.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1954_15200.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
           let env1 =
             let uu___1954_15203 = env  in
             let uu____15204 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1954_15203.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1954_15203.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1954_15203.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1954_15203.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1954_15203.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1954_15203.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1954_15203.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1954_15203.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1954_15203.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1954_15203.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1954_15203.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1954_15203.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1954_15203.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1954_15203.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1954_15203.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1954_15203.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1954_15203.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1954_15203.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1954_15203.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1954_15203.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1954_15203.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1954_15203.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1954_15203.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1954_15203.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1954_15203.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1954_15203.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1954_15203.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1954_15203.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1954_15203.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1954_15203.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1954_15203.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1954_15203.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1954_15203.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1954_15203.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____15204;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1954_15203.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1954_15203.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1954_15203.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1954_15203.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1954_15203.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1954_15203.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1954_15203.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1954_15203.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1954_15203.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions
           uu____15205) ->
           let env1 =
             let uu___1954_15208 = env  in
             let uu____15209 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1954_15208.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1954_15208.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1954_15208.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1954_15208.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1954_15208.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1954_15208.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1954_15208.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1954_15208.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1954_15208.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1954_15208.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1954_15208.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1954_15208.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1954_15208.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1954_15208.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1954_15208.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1954_15208.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1954_15208.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1954_15208.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1954_15208.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1954_15208.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1954_15208.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1954_15208.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1954_15208.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1954_15208.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1954_15208.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1954_15208.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1954_15208.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1954_15208.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1954_15208.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1954_15208.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1954_15208.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1954_15208.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1954_15208.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1954_15208.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____15209;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1954_15208.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1954_15208.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1954_15208.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1954_15208.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1954_15208.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1954_15208.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1954_15208.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1954_15208.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1954_15208.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____15210) ->
           let env1 =
             let uu___1954_15215 = env  in
             let uu____15216 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1954_15215.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1954_15215.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1954_15215.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1954_15215.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1954_15215.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1954_15215.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1954_15215.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1954_15215.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1954_15215.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1954_15215.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1954_15215.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1954_15215.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1954_15215.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1954_15215.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1954_15215.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1954_15215.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1954_15215.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1954_15215.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1954_15215.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1954_15215.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1954_15215.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1954_15215.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1954_15215.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1954_15215.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1954_15215.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1954_15215.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1954_15215.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1954_15215.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1954_15215.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1954_15215.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1954_15215.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1954_15215.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1954_15215.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1954_15215.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____15216;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1954_15215.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1954_15215.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1954_15215.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1954_15215.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1954_15215.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1954_15215.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1954_15215.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1954_15215.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1954_15215.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver )
           ->
           ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
              ();
            env)
       | FStar_Syntax_Syntax.Sig_pragma uu____15218 -> env
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15219 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____15229 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____15229) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____15230,uu____15231,uu____15232) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_15237  ->
                   match uu___5_15237 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____15240 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____15242,uu____15243) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_15252  ->
                   match uu___5_15252 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____15255 -> false))
           -> env
       | uu____15257 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____15326 se =
        match uu____15326 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____15379 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____15379
              then
                let uu____15382 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____15382
              else ());
             (let uu____15387 = tc_decl env1 se  in
              match uu____15387 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____15440 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____15440
                             then
                               let uu____15444 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____15444
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____15460 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____15460
                             then
                               let uu____15464 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____15464
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
                    (let uu____15481 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____15481
                     then
                       let uu____15486 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____15495 =
                                  let uu____15497 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____15497 "\n"  in
                                Prims.op_Hat s uu____15495) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____15486
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____15507 =
                       let uu____15516 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____15516
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____15558 se1 =
                            match uu____15558 with
                            | (exports1,hidden1) ->
                                let uu____15586 = for_export env3 hidden1 se1
                                   in
                                (match uu____15586 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____15507 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____15740 = acc  in
        match uu____15740 with
        | (uu____15775,uu____15776,env1,uu____15778) ->
            let uu____15791 =
              FStar_Util.record_time
                (fun uu____15838  -> process_one_decl acc se)
               in
            (match uu____15791 with
             | (r,ms_elapsed) ->
                 ((let uu____15904 =
                     ((FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TCDeclTime"))
                        ||
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.attr_eq
                              FStar_Syntax_Util.tcdecltime_attr)
                           se.FStar_Syntax_Syntax.sigattrs))
                       || (FStar_Options.timing ())
                      in
                   if uu____15904
                   then
                     let uu____15908 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____15910 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____15908 uu____15910
                   else ());
                  r))
         in
      let uu____15915 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____15915 with
      | (ses1,exports,env1,uu____15963) ->
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
          let uu___2051_16001 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2051_16001.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2051_16001.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2051_16001.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2051_16001.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2051_16001.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2051_16001.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2051_16001.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2051_16001.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2051_16001.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2051_16001.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___2051_16001.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___2051_16001.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___2051_16001.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2051_16001.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2051_16001.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___2051_16001.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2051_16001.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___2051_16001.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2051_16001.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___2051_16001.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___2051_16001.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___2051_16001.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2051_16001.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2051_16001.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2051_16001.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2051_16001.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2051_16001.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2051_16001.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2051_16001.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2051_16001.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2051_16001.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2051_16001.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2051_16001.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2051_16001.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___2051_16001.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2051_16001.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2051_16001.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2051_16001.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2051_16001.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2051_16001.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2051_16001.FStar_TypeChecker_Env.strict_args_tab)
          }  in
        let check_term lid univs1 t =
          let uu____16021 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____16021 with
          | (univs2,t1) ->
              ((let uu____16029 =
                  let uu____16031 =
                    let uu____16037 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____16037  in
                  FStar_All.pipe_left uu____16031
                    (FStar_Options.Other "Exports")
                   in
                if uu____16029
                then
                  let uu____16041 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____16043 =
                    let uu____16045 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____16045
                      (FStar_String.concat ", ")
                     in
                  let uu____16062 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____16041 uu____16043 uu____16062
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____16068 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____16068 (fun a2  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____16094 =
             let uu____16096 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____16098 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____16096 uu____16098
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____16094);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16109) ->
              let uu____16118 =
                let uu____16120 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____16120  in
              if uu____16118
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____16134,uu____16135) ->
              let t =
                let uu____16147 =
                  let uu____16154 =
                    let uu____16155 =
                      let uu____16170 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____16170)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____16155  in
                  FStar_Syntax_Syntax.mk uu____16154  in
                uu____16147 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____16186,uu____16187,uu____16188) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____16198 =
                let uu____16200 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____16200  in
              if uu____16198 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____16208,lbs),uu____16210) ->
              let uu____16221 =
                let uu____16223 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____16223  in
              if uu____16221
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
              let uu____16246 =
                let uu____16248 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____16248  in
              if uu____16246
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____16269 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____16270 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____16277 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____16278 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____16279 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____16280 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____16287 -> ()  in
        let uu____16288 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____16288 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____16394) -> true
             | uu____16396 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____16426 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____16465 ->
                   let uu____16466 =
                     let uu____16473 =
                       let uu____16474 =
                         let uu____16489 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____16489)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____16474  in
                     FStar_Syntax_Syntax.mk uu____16473  in
                   uu____16466 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____16506,uu____16507) ->
            let s1 =
              let uu___2177_16517 = s  in
              let uu____16518 =
                let uu____16519 =
                  let uu____16526 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____16526)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____16519  in
              let uu____16527 =
                let uu____16530 =
                  let uu____16533 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____16533  in
                FStar_Syntax_Syntax.Assumption :: uu____16530  in
              {
                FStar_Syntax_Syntax.sigel = uu____16518;
                FStar_Syntax_Syntax.sigrng =
                  (uu___2177_16517.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____16527;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2177_16517.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___2177_16517.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____16536 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____16561 lbdef =
        match uu____16561 with
        | (uvs,t) ->
            let attrs =
              let uu____16572 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____16572
              then
                let uu____16577 =
                  let uu____16578 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____16578
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____16577 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___2190_16581 = s  in
            let uu____16582 =
              let uu____16585 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____16585  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___2190_16581.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____16582;
              FStar_Syntax_Syntax.sigmeta =
                (uu___2190_16581.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____16603 -> failwith "Impossible!"  in
        let c_opt =
          let uu____16610 = FStar_Syntax_Util.is_unit t  in
          if uu____16610
          then
            let uu____16617 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____16617
          else
            (let uu____16624 =
               let uu____16625 = FStar_Syntax_Subst.compress t  in
               uu____16625.FStar_Syntax_Syntax.n  in
             match uu____16624 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____16632,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____16656 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____16668 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____16668
            then false
            else
              (let uu____16675 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____16675
               then true
               else
                 (let uu____16682 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____16682))
         in
      let extract_sigelt s =
        (let uu____16694 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____16694
         then
           let uu____16697 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____16697
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____16704 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____16724 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____16743 ->
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
                             (lid,uu____16789,uu____16790,uu____16791,uu____16792,uu____16793)
                             ->
                             ((let uu____16803 =
                                 let uu____16806 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____16806  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____16803);
                              (let uu____16855 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____16855 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____16859,uu____16860,uu____16861,uu____16862,uu____16863)
                             ->
                             ((let uu____16871 =
                                 let uu____16874 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____16874  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____16871);
                              sigelts1)
                         | uu____16923 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____16932 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____16932
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____16942 =
                    let uu___2254_16943 = s  in
                    let uu____16944 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2254_16943.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2254_16943.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____16944;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2254_16943.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2254_16943.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____16942])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____16955 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____16955
             then []
             else
               (let uu____16962 = lbs  in
                match uu____16962 with
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
                        (fun uu____17024  ->
                           match uu____17024 with
                           | (uu____17032,t,uu____17034) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____17051  ->
                             match uu____17051 with
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
                           (fun uu____17078  ->
                              match uu____17078 with
                              | (uu____17086,t,uu____17088) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____17100,uu____17101) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____17109 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____17138 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____17138) uu____17109
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____17142 =
                    let uu___2296_17143 = s  in
                    let uu____17144 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2296_17143.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2296_17143.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____17144;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2296_17143.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2296_17143.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____17142]
                else [])
             else
               (let uu____17151 =
                  let uu___2298_17152 = s  in
                  let uu____17153 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___2298_17152.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___2298_17152.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____17153;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___2298_17152.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___2298_17152.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____17151])
         | FStar_Syntax_Syntax.Sig_new_effect uu____17156 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____17157 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____17158 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____17159 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____17172 -> [s])
         in
      let uu___2310_17173 = m  in
      let uu____17174 =
        let uu____17175 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____17175 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___2310_17173.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____17174;
        FStar_Syntax_Syntax.exports =
          (uu___2310_17173.FStar_Syntax_Syntax.exports);
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
        (fun uu____17226  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____17273  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____17288 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____17288
  
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
      (let uu____17377 = FStar_Options.debug_any ()  in
       if uu____17377
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
         let uu___2335_17393 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___2335_17393.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___2335_17393.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___2335_17393.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___2335_17393.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___2335_17393.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___2335_17393.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___2335_17393.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___2335_17393.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___2335_17393.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___2335_17393.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___2335_17393.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___2335_17393.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___2335_17393.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___2335_17393.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___2335_17393.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___2335_17393.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___2335_17393.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___2335_17393.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___2335_17393.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___2335_17393.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___2335_17393.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___2335_17393.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___2335_17393.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___2335_17393.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___2335_17393.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___2335_17393.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___2335_17393.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___2335_17393.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___2335_17393.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___2335_17393.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___2335_17393.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___2335_17393.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___2335_17393.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___2335_17393.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___2335_17393.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___2335_17393.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___2335_17393.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___2335_17393.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___2335_17393.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___2335_17393.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___2335_17393.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___2335_17393.FStar_TypeChecker_Env.strict_args_tab)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____17395 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____17395 with
       | (ses,exports,env3) ->
           ((let uu___2343_17428 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___2343_17428.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___2343_17428.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___2343_17428.FStar_Syntax_Syntax.is_interface)
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
        let uu____17457 = tc_decls env decls  in
        match uu____17457 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___2352_17488 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___2352_17488.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___2352_17488.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___2352_17488.FStar_Syntax_Syntax.is_interface)
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
        let uu____17549 = tc_partial_modul env01 m  in
        match uu____17549 with
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
                (let uu____17586 = FStar_Errors.get_err_count ()  in
                 uu____17586 = Prims.int_zero)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____17597 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____17597
                then
                  let uu____17601 =
                    let uu____17603 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____17603 then "" else " (in lax mode) "  in
                  let uu____17611 =
                    let uu____17613 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____17613
                    then
                      let uu____17617 =
                        let uu____17619 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.op_Hat uu____17619 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____17617
                    else ""  in
                  let uu____17626 =
                    let uu____17628 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____17628
                    then
                      let uu____17632 =
                        let uu____17634 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____17634 "\n"  in
                      Prims.op_Hat "\nto: " uu____17632
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____17601
                    uu____17611 uu____17626
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___2378_17648 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2378_17648.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2378_17648.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2378_17648.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2378_17648.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2378_17648.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2378_17648.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2378_17648.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2378_17648.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2378_17648.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2378_17648.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2378_17648.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2378_17648.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2378_17648.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2378_17648.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2378_17648.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2378_17648.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2378_17648.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2378_17648.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2378_17648.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2378_17648.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2378_17648.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2378_17648.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2378_17648.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2378_17648.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2378_17648.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2378_17648.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2378_17648.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2378_17648.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2378_17648.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2378_17648.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2378_17648.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___2378_17648.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2378_17648.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2378_17648.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2378_17648.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2378_17648.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2378_17648.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2378_17648.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2378_17648.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2378_17648.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2378_17648.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2378_17648.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2378_17648.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let en02 =
                    let uu___2381_17650 = en01  in
                    let uu____17651 =
                      let uu____17666 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____17666, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2381_17650.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2381_17650.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2381_17650.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2381_17650.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2381_17650.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2381_17650.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2381_17650.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2381_17650.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2381_17650.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2381_17650.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2381_17650.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2381_17650.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2381_17650.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2381_17650.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2381_17650.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2381_17650.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2381_17650.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2381_17650.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2381_17650.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2381_17650.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2381_17650.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2381_17650.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2381_17650.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2381_17650.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2381_17650.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2381_17650.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2381_17650.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2381_17650.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2381_17650.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2381_17650.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2381_17650.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____17651;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2381_17650.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2381_17650.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2381_17650.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2381_17650.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2381_17650.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2381_17650.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2381_17650.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2381_17650.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2381_17650.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___2381_17650.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2381_17650.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2381_17650.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let uu____17712 =
                    let uu____17714 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____17714  in
                  if uu____17712
                  then
                    ((let uu____17718 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____17718 (fun a3  -> ()));
                     en02)
                  else en02  in
                let uu____17722 = tc_modul en0 modul_iface true  in
                match uu____17722 with
                | (modul_iface1,env) ->
                    ((let uu___2390_17735 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___2390_17735.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___2390_17735.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___2390_17735.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___2392_17739 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___2392_17739.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___2392_17739.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___2392_17739.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____17742 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____17742 FStar_Util.smap_clear);
               (let uu____17778 =
                  ((let uu____17782 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____17782) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____17785 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____17785)
                   in
                if uu____17778 then check_exports env modul exports else ());
               (let uu____17791 =
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____17791 (fun a4  -> ()));
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
        let uu____17806 =
          let uu____17808 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____17808  in
        push_context env uu____17806  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____17829 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____17840 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____17840 with | (uu____17847,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____17872 = FStar_Options.debug_any ()  in
         if uu____17872
         then
           let uu____17875 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____17875
         else ());
        (let uu____17887 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____17887
         then
           let uu____17890 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____17890
         else ());
        (let env1 =
           let uu___2422_17896 = env  in
           let uu____17897 =
             let uu____17899 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____17899  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___2422_17896.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___2422_17896.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___2422_17896.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___2422_17896.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___2422_17896.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___2422_17896.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___2422_17896.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___2422_17896.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___2422_17896.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___2422_17896.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___2422_17896.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___2422_17896.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___2422_17896.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___2422_17896.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___2422_17896.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___2422_17896.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___2422_17896.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___2422_17896.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___2422_17896.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___2422_17896.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____17897;
             FStar_TypeChecker_Env.lax_universes =
               (uu___2422_17896.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___2422_17896.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___2422_17896.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___2422_17896.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___2422_17896.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___2422_17896.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___2422_17896.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___2422_17896.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___2422_17896.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___2422_17896.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___2422_17896.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___2422_17896.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___2422_17896.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___2422_17896.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___2422_17896.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___2422_17896.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___2422_17896.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___2422_17896.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___2422_17896.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___2422_17896.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___2422_17896.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___2422_17896.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___2422_17896.FStar_TypeChecker_Env.strict_args_tab)
           }  in
         let uu____17901 = tc_modul env1 m b  in
         match uu____17901 with
         | (m1,env2) ->
             ((let uu____17913 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____17913
               then
                 let uu____17916 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____17916
               else ());
              (let uu____17922 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____17922
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
                         let uu____17960 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____17960 with
                         | (univnames1,e) ->
                             let uu___2444_17967 = lb  in
                             let uu____17968 =
                               let uu____17971 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____17971 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2444_17967.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2444_17967.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___2444_17967.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2444_17967.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____17968;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2444_17967.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2444_17967.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___2446_17972 = se  in
                       let uu____17973 =
                         let uu____17974 =
                           let uu____17981 =
                             let uu____17982 = FStar_List.map update lbs  in
                             (b1, uu____17982)  in
                           (uu____17981, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____17974  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____17973;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___2446_17972.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___2446_17972.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___2446_17972.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___2446_17972.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____17990 -> se  in
                 let normalized_module =
                   let uu___2450_17992 = m1  in
                   let uu____17993 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___2450_17992.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____17993;
                     FStar_Syntax_Syntax.exports =
                       (uu___2450_17992.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___2450_17992.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____17994 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____17994
               else ());
              (m1, env2)))
  