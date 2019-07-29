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
  
let (open_and_check :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp))
  =
  fun env  ->
    fun eff_binders  ->
      fun other_binders  ->
        fun t  ->
          let subst1 =
            FStar_Syntax_Subst.opening_of_binders
              (FStar_List.append eff_binders other_binders)
             in
          let t1 = FStar_Syntax_Subst.subst subst1 t  in
          let uu____505 = FStar_TypeChecker_TcTerm.tc_term env t1  in
          match uu____505 with | (t2,comp,uu____518) -> (t2, comp)
  
let (elaborate_and_star :
  FStar_TypeChecker_DMFF.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.tscheme ->
          (FStar_TypeChecker_DMFF.env * FStar_Syntax_Syntax.typ *
            FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun dmff_env  ->
    fun eff_binders  ->
      fun other_binders  ->
        fun item  ->
          let env = FStar_TypeChecker_DMFF.get_env dmff_env  in
          let uu____557 = item  in
          match uu____557 with
          | (u_item,item1) ->
              let uu____576 =
                open_and_check env eff_binders other_binders item1  in
              (match uu____576 with
               | (item2,item_comp) ->
                   ((let uu____592 =
                       let uu____594 =
                         FStar_Syntax_Util.is_total_lcomp item_comp  in
                       Prims.op_Negation uu____594  in
                     if uu____592
                     then
                       let uu____597 =
                         let uu____603 =
                           let uu____605 =
                             FStar_Syntax_Print.term_to_string item2  in
                           let uu____607 =
                             FStar_Syntax_Print.lcomp_to_string item_comp  in
                           FStar_Util.format2
                             "Computation for [%s] is not total : %s !"
                             uu____605 uu____607
                            in
                         (FStar_Errors.Fatal_ComputationNotTotal, uu____603)
                          in
                       FStar_Errors.raise_err uu____597
                     else ());
                    (let uu____613 =
                       FStar_TypeChecker_DMFF.star_expr dmff_env item2  in
                     match uu____613 with
                     | (item_t,item_wp,item_elab) ->
                         let uu____631 = recheck_debug "*" env item_wp  in
                         let uu____633 = recheck_debug "_" env item_elab  in
                         (dmff_env, item_t, item_wp, item_elab))))
  
let (cps_and_elaborate_ed :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun ed  ->
      let signature = ed.FStar_Syntax_Syntax.signature  in
      let uu____657 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders signature
         in
      match uu____657 with
      | (effect_binders_un,signature_un) ->
          let uu____674 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____674 with
           | (effect_binders,env1,uu____693) ->
               let uu____694 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____694 with
                | (signature1,uu____710) ->
                    let raise_error1 uu____726 =
                      match uu____726 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature1.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____762  ->
                           match uu____762 with
                           | (bv,qual) ->
                               let uu____781 =
                                 let uu___124_782 = bv  in
                                 let uu____783 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___124_782.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___124_782.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____783
                                 }  in
                               (uu____781, qual)) effect_binders
                       in
                    let uu____788 =
                      let uu____795 =
                        let uu____796 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____796.FStar_Syntax_Syntax.n  in
                      match uu____795 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____806)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____838 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____788 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____864 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____864
                           then
                             let uu____867 =
                               let uu____870 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____870  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____867
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature1.FStar_Syntax_Syntax.pos
                            in
                         let uu____882 =
                           open_and_check env1 effect_binders1 []
                             (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                            in
                         (match uu____882 with
                          | (repr,_comp) ->
                              ((let uu____906 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____906
                                then
                                  let uu____910 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____910
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env1
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       env1 FStar_Range.dummyRange)
                                   in
                                let is_unk t =
                                  let uu____923 =
                                    let uu____924 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____924.FStar_Syntax_Syntax.n  in
                                  match uu____923 with
                                  | FStar_Syntax_Syntax.Tm_unknown  -> true
                                  | uu____929 -> false  in
                                let uu____931 =
                                  let uu____936 =
                                    is_unk
                                      (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m
                                     in
                                  if uu____936
                                  then
                                    let uu____943 =
                                      FStar_TypeChecker_DMFF.star_type
                                        dmff_env repr
                                       in
                                    ((let uu___153_945 = ed  in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___153_945.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___153_945.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___153_945.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___153_945.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.spec =
                                          (uu___153_945.FStar_Syntax_Syntax.spec);
                                        FStar_Syntax_Syntax.signature =
                                          (uu___153_945.FStar_Syntax_Syntax.signature);
                                        FStar_Syntax_Syntax.if_then_else =
                                          (uu___153_945.FStar_Syntax_Syntax.if_then_else);
                                        FStar_Syntax_Syntax.ite_wp =
                                          (uu___153_945.FStar_Syntax_Syntax.ite_wp);
                                        FStar_Syntax_Syntax.stronger =
                                          (uu___153_945.FStar_Syntax_Syntax.stronger);
                                        FStar_Syntax_Syntax.close_wp =
                                          (uu___153_945.FStar_Syntax_Syntax.close_wp);
                                        FStar_Syntax_Syntax.trivial =
                                          (uu___153_945.FStar_Syntax_Syntax.trivial);
                                        FStar_Syntax_Syntax.repr =
                                          (uu___153_945.FStar_Syntax_Syntax.repr);
                                        FStar_Syntax_Syntax.elaborated =
                                          (uu___153_945.FStar_Syntax_Syntax.elaborated);
                                        FStar_Syntax_Syntax.spec_dm4f = true;
                                        FStar_Syntax_Syntax.interp =
                                          (uu___153_945.FStar_Syntax_Syntax.interp);
                                        FStar_Syntax_Syntax.mrelation =
                                          (uu___153_945.FStar_Syntax_Syntax.mrelation);
                                        FStar_Syntax_Syntax.actions =
                                          (uu___153_945.FStar_Syntax_Syntax.actions);
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___153_945.FStar_Syntax_Syntax.eff_attrs)
                                      }), uu____943)
                                  else
                                    (ed,
                                      ((ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m))
                                   in
                                match uu____931 with
                                | (ed1,wp_type) ->
                                    let wp_type1 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.UnfoldUntil
                                           FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.AllowUnboundUniverses]
                                        env1 wp_type
                                       in
                                    let uu____962 =
                                      recheck_debug "*" env1 wp_type1  in
                                    let wp_a =
                                      let uu____965 =
                                        let uu____966 =
                                          let uu____967 =
                                            let uu____984 =
                                              let uu____995 =
                                                let uu____1004 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a1
                                                   in
                                                let uu____1007 =
                                                  FStar_Syntax_Syntax.as_implicit
                                                    false
                                                   in
                                                (uu____1004, uu____1007)  in
                                              [uu____995]  in
                                            (wp_type1, uu____984)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____967
                                           in
                                        mk1 uu____966  in
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Beta] env1
                                        uu____965
                                       in
                                    let effect_signature =
                                      let binders =
                                        let uu____1055 =
                                          let uu____1062 =
                                            FStar_Syntax_Syntax.as_implicit
                                              false
                                             in
                                          (a1, uu____1062)  in
                                        let uu____1068 =
                                          let uu____1077 =
                                            let uu____1084 =
                                              FStar_Syntax_Syntax.gen_bv
                                                "dijkstra_wp"
                                                FStar_Pervasives_Native.None
                                                wp_a
                                               in
                                            FStar_All.pipe_right uu____1084
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          [uu____1077]  in
                                        uu____1055 :: uu____1068  in
                                      let binders1 =
                                        FStar_Syntax_Subst.close_binders
                                          binders
                                         in
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (binders1, effect_marker))
                                       in
                                    let uu____1121 =
                                      recheck_debug
                                        "turned into the effect signature"
                                        env1 effect_signature
                                       in
                                    let sigelts = FStar_Util.mk_ref []  in
                                    let mk_lid name =
                                      FStar_Syntax_Util.dm4f_lid ed1 name  in
                                    let uu____1138 =
                                      if ed1.FStar_Syntax_Syntax.spec_dm4f
                                      then
                                        let uu____1160 =
                                          elaborate_and_star dmff_env
                                            effect_binders1 []
                                            (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                           in
                                        match uu____1160 with
                                        | (dmff_env1,uu____1186,bind_wp,bind_elab)
                                            ->
                                            let bind_wp1 =
                                              let uu____1192 =
                                                is_unk
                                                  (FStar_Pervasives_Native.snd
                                                     (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind)
                                                 in
                                              if uu____1192
                                              then
                                                let uu____1201 =
                                                  let uu____1202 =
                                                    let uu____1209 =
                                                      FStar_Syntax_Syntax.tabbrev
                                                        FStar_Parser_Const.range_lid
                                                       in
                                                    FStar_Syntax_Syntax.null_binder
                                                      uu____1209
                                                     in
                                                  [uu____1202]  in
                                                FStar_Syntax_Util.abs
                                                  uu____1201 bind_wp
                                                  FStar_Pervasives_Native.None
                                              else
                                                FStar_Pervasives_Native.snd
                                                  (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                               in
                                            (dmff_env1, bind_wp1, bind_elab)
                                      else
                                        (dmff_env,
                                          (FStar_Pervasives_Native.snd
                                             (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind),
                                          (FStar_Pervasives_Native.snd
                                             (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind))
                                       in
                                    (match uu____1138 with
                                     | (dmff_env1,bind_wp,bind_elab) ->
                                         let uu____1267 =
                                           let uu____1278 =
                                             ed1.FStar_Syntax_Syntax.spec_dm4f
                                               &&
                                               (is_unk
                                                  (FStar_Pervasives_Native.snd
                                                     (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret))
                                              in
                                           if uu____1278
                                           then
                                             let uu____1295 =
                                               elaborate_and_star dmff_env1
                                                 effect_binders1 []
                                                 (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                                in
                                             match uu____1295 with
                                             | (dmff_env2,uu____1321,return_wp,return_elab)
                                                 ->
                                                 let return_wp1 =
                                                   let uu____1327 =
                                                     is_unk
                                                       (FStar_Pervasives_Native.snd
                                                          (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret)
                                                      in
                                                   if uu____1327
                                                   then return_wp
                                                   else
                                                     FStar_Pervasives_Native.snd
                                                       (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                                    in
                                                 (dmff_env2, return_wp1,
                                                   return_elab)
                                           else
                                             (dmff_env1,
                                               (FStar_Pervasives_Native.snd
                                                  (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret),
                                               (FStar_Pervasives_Native.snd
                                                  (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret))
                                            in
                                         (match uu____1267 with
                                          | (dmff_env2,return_wp,return_elab)
                                              ->
                                              let rc_gtot =
                                                {
                                                  FStar_Syntax_Syntax.residual_effect
                                                    =
                                                    FStar_Parser_Const.effect_GTot_lid;
                                                  FStar_Syntax_Syntax.residual_typ
                                                    =
                                                    FStar_Pervasives_Native.None;
                                                  FStar_Syntax_Syntax.residual_flags
                                                    = []
                                                }  in
                                              let lift_from_pure_wp =
                                                let pure_wp_type t =
                                                  FStar_TypeChecker_DMFF.double_star
                                                    t
                                                   in
                                                let b1 =
                                                  let uu____1394 =
                                                    FStar_Syntax_Syntax.new_bv
                                                      FStar_Pervasives_Native.None
                                                      FStar_Syntax_Util.ktype
                                                     in
                                                  FStar_Syntax_Syntax.mk_binder
                                                    uu____1394
                                                   in
                                                let t_b1 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    (FStar_Pervasives_Native.fst
                                                       b1)
                                                   in
                                                let bwp =
                                                  let uu____1399 =
                                                    let uu____1400 =
                                                      pure_wp_type t_b1  in
                                                    FStar_Syntax_Syntax.new_bv
                                                      FStar_Pervasives_Native.None
                                                      uu____1400
                                                     in
                                                  FStar_Syntax_Syntax.mk_binder
                                                    uu____1399
                                                   in
                                                let t_wp =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    (FStar_Pervasives_Native.fst
                                                       bwp)
                                                   in
                                                let b2 =
                                                  let uu____1405 =
                                                    FStar_Syntax_Syntax.new_bv
                                                      FStar_Pervasives_Native.None
                                                      t_b1
                                                     in
                                                  FStar_Syntax_Syntax.mk_binder
                                                    uu____1405
                                                   in
                                                let t_b2 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    (FStar_Pervasives_Native.fst
                                                       b2)
                                                   in
                                                let t =
                                                  let uu____1410 =
                                                    let uu____1411 =
                                                      let uu____1422 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t_b1
                                                         in
                                                      [uu____1422]  in
                                                    FStar_Syntax_Util.mk_app
                                                      wp_type1 uu____1411
                                                     in
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 uu____1410
                                                   in
                                                let uu____1447 =
                                                  FStar_Syntax_Util.arrow_formals_comp
                                                    t
                                                   in
                                                match uu____1447 with
                                                | (bs,r) ->
                                                    let t00 =
                                                      let uu____1483 =
                                                        let uu____1494 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            t_b1
                                                           in
                                                        let uu____1501 =
                                                          let uu____1510 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              t_b2
                                                             in
                                                          let uu____1517 =
                                                            FStar_List.map
                                                              (fun uu____1542
                                                                  ->
                                                                 match uu____1542
                                                                 with
                                                                 | (bv,q) ->
                                                                    let uu____1561
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv  in
                                                                    (uu____1561,
                                                                    q)) bs
                                                             in
                                                          uu____1510 ::
                                                            uu____1517
                                                           in
                                                        uu____1494 ::
                                                          uu____1501
                                                         in
                                                      FStar_Syntax_Util.mk_app
                                                        return_wp uu____1483
                                                       in
                                                    let t0 =
                                                      FStar_Syntax_Util.abs
                                                        [b2] t00
                                                        FStar_Pervasives_Native.None
                                                       in
                                                    let t1 =
                                                      let uu____1594 =
                                                        let uu____1597 =
                                                          let uu____1608 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              t0
                                                             in
                                                          [uu____1608]  in
                                                        FStar_Syntax_Util.mk_app
                                                          t_wp uu____1597
                                                         in
                                                      FStar_Syntax_Util.abs
                                                        bs uu____1594
                                                        FStar_Pervasives_Native.None
                                                       in
                                                    let t2 =
                                                      FStar_Syntax_Util.abs
                                                        [b1; bwp] t1
                                                        FStar_Pervasives_Native.None
                                                       in
                                                    let t21 =
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Env.Beta]
                                                        env1 t2
                                                       in
                                                    ((let uu____1656 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          (FStar_Options.Other
                                                             "ED")
                                                         in
                                                      if uu____1656
                                                      then
                                                        let uu____1661 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t21
                                                           in
                                                        FStar_Util.print1
                                                          "elaborated lift from PURE = %s\n"
                                                          uu____1661
                                                      else ());
                                                     t21)
                                                 in
                                              let apply_close t =
                                                if
                                                  (FStar_List.length
                                                     effect_binders1)
                                                    = Prims.int_zero
                                                then t
                                                else
                                                  (let uu____1691 =
                                                     let uu____1692 =
                                                       let uu____1693 =
                                                         let uu____1710 =
                                                           let uu____1721 =
                                                             FStar_Syntax_Util.args_of_binders
                                                               effect_binders1
                                                              in
                                                           FStar_Pervasives_Native.snd
                                                             uu____1721
                                                            in
                                                         (t, uu____1710)  in
                                                       FStar_Syntax_Syntax.Tm_app
                                                         uu____1693
                                                        in
                                                     mk1 uu____1692  in
                                                   FStar_Syntax_Subst.close
                                                     effect_binders1
                                                     uu____1691)
                                                 in
                                              let register name item =
                                                let uu____1755 =
                                                  let uu____1760 =
                                                    mk_lid name  in
                                                  let uu____1761 =
                                                    FStar_Syntax_Util.abs
                                                      effect_binders1 item
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  FStar_TypeChecker_Util.mk_toplevel_definition
                                                    env1 uu____1760
                                                    uu____1761
                                                   in
                                                match uu____1755 with
                                                | (sigelt,fv) ->
                                                    ((let uu____1765 =
                                                        let uu____1768 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____1768
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____1765);
                                                     fv)
                                                 in
                                              let lift_from_pure_wp1 =
                                                register "lift_from_pure"
                                                  lift_from_pure_wp
                                                 in
                                              let return_wp1 =
                                                register "return_wp"
                                                  return_wp
                                                 in
                                              ((let uu____1822 =
                                                  let uu____1825 =
                                                    FStar_Syntax_Syntax.mk_sigelt
                                                      (FStar_Syntax_Syntax.Sig_pragma
                                                         (FStar_Syntax_Syntax.PushOptions
                                                            (FStar_Pervasives_Native.Some
                                                               "--admit_smt_queries true")))
                                                     in
                                                  let uu____1828 =
                                                    FStar_ST.op_Bang sigelts
                                                     in
                                                  uu____1825 :: uu____1828
                                                   in
                                                FStar_ST.op_Colon_Equals
                                                  sigelts uu____1822);
                                               (let return_elab1 =
                                                  register "return_elab"
                                                    return_elab
                                                   in
                                                (let uu____1880 =
                                                   let uu____1883 =
                                                     FStar_Syntax_Syntax.mk_sigelt
                                                       (FStar_Syntax_Syntax.Sig_pragma
                                                          FStar_Syntax_Syntax.PopOptions)
                                                      in
                                                   let uu____1884 =
                                                     FStar_ST.op_Bang sigelts
                                                      in
                                                   uu____1883 :: uu____1884
                                                    in
                                                 FStar_ST.op_Colon_Equals
                                                   sigelts uu____1880);
                                                (let bind_wp1 =
                                                   register "bind_wp" bind_wp
                                                    in
                                                 (let uu____1936 =
                                                    let uu____1939 =
                                                      FStar_Syntax_Syntax.mk_sigelt
                                                        (FStar_Syntax_Syntax.Sig_pragma
                                                           (FStar_Syntax_Syntax.PushOptions
                                                              (FStar_Pervasives_Native.Some
                                                                 "--admit_smt_queries true")))
                                                       in
                                                    let uu____1942 =
                                                      FStar_ST.op_Bang
                                                        sigelts
                                                       in
                                                    uu____1939 :: uu____1942
                                                     in
                                                  FStar_ST.op_Colon_Equals
                                                    sigelts uu____1936);
                                                 (let bind_elab1 =
                                                    register "bind_elab"
                                                      bind_elab
                                                     in
                                                  (let uu____1994 =
                                                     let uu____1997 =
                                                       FStar_Syntax_Syntax.mk_sigelt
                                                         (FStar_Syntax_Syntax.Sig_pragma
                                                            FStar_Syntax_Syntax.PopOptions)
                                                        in
                                                     let uu____1998 =
                                                       FStar_ST.op_Bang
                                                         sigelts
                                                        in
                                                     uu____1997 :: uu____1998
                                                      in
                                                   FStar_ST.op_Colon_Equals
                                                     sigelts uu____1994);
                                                  (let uu____2047 =
                                                     FStar_List.fold_left
                                                       (fun uu____2087  ->
                                                          fun action  ->
                                                            match uu____2087
                                                            with
                                                            | (dmff_env3,actions)
                                                                ->
                                                                let params_un
                                                                  =
                                                                  FStar_Syntax_Subst.open_binders
                                                                    action.FStar_Syntax_Syntax.action_params
                                                                   in
                                                                let uu____2108
                                                                  =
                                                                  let uu____2115
                                                                    =
                                                                    FStar_TypeChecker_DMFF.get_env
                                                                    dmff_env3
                                                                     in
                                                                  FStar_TypeChecker_TcTerm.tc_tparams
                                                                    uu____2115
                                                                    params_un
                                                                   in
                                                                (match uu____2108
                                                                 with
                                                                 | (action_params,env',uu____2124)
                                                                    ->
                                                                    let action_params1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____2150
                                                                     ->
                                                                    match uu____2150
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____2169
                                                                    =
                                                                    let uu___247_2170
                                                                    = bv  in
                                                                    let uu____2171
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___247_2170.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___247_2170.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2171
                                                                    }  in
                                                                    (uu____2169,
                                                                    qual))
                                                                    action_params
                                                                     in
                                                                    let dmff_env'
                                                                    =
                                                                    FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'  in
                                                                    let uu____2177
                                                                    =
                                                                    elaborate_and_star
                                                                    dmff_env'
                                                                    effect_binders1
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                     in
                                                                    (match uu____2177
                                                                    with
                                                                    | 
                                                                    (dmff_env4,action_t,action_wp,action_elab)
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
                                                                    uu____2220
                                                                    ->
                                                                    let uu____2221
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____2221
                                                                     in
                                                                    ((
                                                                    let uu____2225
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____2225
                                                                    then
                                                                    let uu____2230
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____2233
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____2236
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____2238
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____2230
                                                                    uu____2233
                                                                    uu____2236
                                                                    uu____2238
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
                                                                    let uu____2247
                                                                    =
                                                                    let uu____2250
                                                                    =
                                                                    let uu___269_2251
                                                                    = action
                                                                     in
                                                                    let uu____2252
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____2253
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___269_2251.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___269_2251.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___269_2251.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2252;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2253
                                                                    }  in
                                                                    uu____2250
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____2247))))))
                                                       (dmff_env2, [])
                                                       ed1.FStar_Syntax_Syntax.actions
                                                      in
                                                   match uu____2047 with
                                                   | (dmff_env3,actions) ->
                                                       let actions1 =
                                                         FStar_List.rev
                                                           actions
                                                          in
                                                       let repr1 =
                                                         if
                                                           Prims.op_Negation
                                                             ed1.FStar_Syntax_Syntax.spec_dm4f
                                                         then
                                                           let repr1 =
                                                             let uu____2292 =
                                                               let uu____2293
                                                                 =
                                                                 FStar_Syntax_Subst.compress
                                                                   repr
                                                                  in
                                                               uu____2293.FStar_Syntax_Syntax.n
                                                                in
                                                             match uu____2292
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_uinst
                                                                 (t,univs1)
                                                                 ->
                                                                 let uu____2304
                                                                   =
                                                                   FStar_List.map
                                                                    (fun
                                                                    uu____2306
                                                                     ->
                                                                    FStar_Syntax_Syntax.U_unknown)
                                                                    univs1
                                                                    in
                                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                                   t
                                                                   uu____2304
                                                             | uu____2307 ->
                                                                 repr
                                                              in
                                                           repr1
                                                         else
                                                           (let wp =
                                                              FStar_Syntax_Syntax.gen_bv
                                                                "wp_a"
                                                                FStar_Pervasives_Native.None
                                                                wp_a
                                                               in
                                                            let binders =
                                                              let uu____2321
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  a1
                                                                 in
                                                              let uu____2328
                                                                =
                                                                let uu____2337
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp
                                                                   in
                                                                [uu____2337]
                                                                 in
                                                              uu____2321 ::
                                                                uu____2328
                                                               in
                                                            let r =
                                                              let uu____2365
                                                                =
                                                                let uu____2368
                                                                  =
                                                                  let uu____2369
                                                                    =
                                                                    let uu____2370
                                                                    =
                                                                    let uu____2387
                                                                    =
                                                                    let uu____2398
                                                                    =
                                                                    let uu____2407
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    a1  in
                                                                    let uu____2410
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                    (uu____2407,
                                                                    uu____2410)
                                                                     in
                                                                    [uu____2398]
                                                                     in
                                                                    (repr,
                                                                    uu____2387)
                                                                     in
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    uu____2370
                                                                     in
                                                                  mk1
                                                                    uu____2369
                                                                   in
                                                                let uu____2446
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    wp
                                                                   in
                                                                FStar_TypeChecker_DMFF.trans_F
                                                                  dmff_env3
                                                                  uu____2368
                                                                  uu____2446
                                                                 in
                                                              FStar_Syntax_Util.abs
                                                                binders
                                                                uu____2365
                                                                FStar_Pervasives_Native.None
                                                               in
                                                            r)
                                                          in
                                                       let uu____2447 =
                                                         recheck_debug "FC"
                                                           env1 repr1
                                                          in
                                                       let repr2 =
                                                         register "repr"
                                                           repr1
                                                          in
                                                       let uu____2451 =
                                                         let uu____2460 =
                                                           let uu____2461 =
                                                             let uu____2464 =
                                                               FStar_Syntax_Subst.compress
                                                                 wp_type1
                                                                in
                                                             FStar_All.pipe_left
                                                               FStar_Syntax_Util.unascribe
                                                               uu____2464
                                                              in
                                                           uu____2461.FStar_Syntax_Syntax.n
                                                            in
                                                         match uu____2460
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_abs
                                                             (type_param::effect_param,arrow1,uu____2478)
                                                             ->
                                                             let uu____2515 =
                                                               let uu____2536
                                                                 =
                                                                 FStar_Syntax_Subst.open_term
                                                                   (type_param
                                                                   ::
                                                                   effect_param)
                                                                   arrow1
                                                                  in
                                                               match uu____2536
                                                               with
                                                               | (b::bs,body)
                                                                   ->
                                                                   (b, bs,
                                                                    body)
                                                               | uu____2604
                                                                   ->
                                                                   failwith
                                                                    "Impossible : open_term nt preserving binders arity"
                                                                in
                                                             (match uu____2515
                                                              with
                                                              | (type_param1,effect_param1,arrow2)
                                                                  ->
                                                                  let uu____2669
                                                                    =
                                                                    let uu____2670
                                                                    =
                                                                    let uu____2673
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Util.unascribe
                                                                    uu____2673
                                                                     in
                                                                    uu____2670.FStar_Syntax_Syntax.n
                                                                     in
                                                                  (match uu____2669
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_arrow
                                                                    (wp_binders,c)
                                                                    ->
                                                                    let uu____2706
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                    (match uu____2706
                                                                    with
                                                                    | 
                                                                    (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2721
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2752
                                                                     ->
                                                                    match uu____2752
                                                                    with
                                                                    | 
                                                                    (bv,uu____2761)
                                                                    ->
                                                                    let uu____2766
                                                                    =
                                                                    let uu____2768
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2768
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2766
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____2721
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
                                                                    let uu____2860
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____2860
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____2870
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____2881
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____2881
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____2891
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____2894
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____2891,
                                                                    uu____2894)))
                                                                   | 
                                                                   uu____2909
                                                                    ->
                                                                    let uu____2910
                                                                    =
                                                                    let uu____2916
                                                                    =
                                                                    let uu____2918
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2918
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____2916)
                                                                     in
                                                                    raise_error1
                                                                    uu____2910))
                                                         | uu____2930 ->
                                                             let uu____2931 =
                                                               let uu____2937
                                                                 =
                                                                 let uu____2939
                                                                   =
                                                                   FStar_Syntax_Print.term_to_string
                                                                    wp_type1
                                                                    in
                                                                 FStar_Util.format1
                                                                   "Impossible: pre/post abs %s"
                                                                   uu____2939
                                                                  in
                                                               (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                                 uu____2937)
                                                                in
                                                             raise_error1
                                                               uu____2931
                                                          in
                                                       (match uu____2451 with
                                                        | (pre,post) ->
                                                            ((let uu____2972
                                                                =
                                                                register
                                                                  "pre" pre
                                                                 in
                                                              ());
                                                             (let uu____2975
                                                                =
                                                                register
                                                                  "post" post
                                                                 in
                                                              ());
                                                             (let uu____2978
                                                                =
                                                                register "wp"
                                                                  wp_type1
                                                                 in
                                                              ());
                                                             (let uu____2981
                                                                =
                                                                FStar_TypeChecker_Env.debug
                                                                  env1
                                                                  (FStar_Options.Other
                                                                    "ED")
                                                                 in
                                                              if uu____2981
                                                              then
                                                                let uu____2985
                                                                  =
                                                                  FStar_Syntax_Print.term_to_string
                                                                    repr2
                                                                   in
                                                                FStar_Util.print1
                                                                  "GGG 14 Representation is: %s\n"
                                                                  uu____2985
                                                              else ());
                                                             (let ed2 =
                                                                let uu___336_2991
                                                                  = ed1  in
                                                                let uu____2992
                                                                  =
                                                                  FStar_Syntax_Subst.close_binders
                                                                    effect_binders1
                                                                   in
                                                                let uu____2993
                                                                  =
                                                                  let uu____2994
                                                                    =
                                                                    let uu____2995
                                                                    =
                                                                    apply_close
                                                                    return_wp1
                                                                     in
                                                                    ([],
                                                                    uu____2995)
                                                                     in
                                                                  let uu____3002
                                                                    =
                                                                    let uu____3003
                                                                    =
                                                                    apply_close
                                                                    bind_wp1
                                                                     in
                                                                    ([],
                                                                    uu____3003)
                                                                     in
                                                                  {
                                                                    FStar_Syntax_Syntax.monad_m
                                                                    =
                                                                    FStar_Syntax_Syntax.tun;
                                                                    FStar_Syntax_Syntax.monad_ret
                                                                    =
                                                                    uu____2994;
                                                                    FStar_Syntax_Syntax.monad_bind
                                                                    =
                                                                    uu____3002
                                                                  }  in
                                                                let uu____3010
                                                                  =
                                                                  FStar_Syntax_Subst.close
                                                                    effect_binders1
                                                                    effect_signature
                                                                   in
                                                                let uu____3011
                                                                  =
                                                                  let uu____3012
                                                                    =
                                                                    apply_close
                                                                    repr2  in
                                                                  let uu____3013
                                                                    =
                                                                    let uu____3014
                                                                    =
                                                                    apply_close
                                                                    return_elab1
                                                                     in
                                                                    ([],
                                                                    uu____3014)
                                                                     in
                                                                  let uu____3021
                                                                    =
                                                                    let uu____3022
                                                                    =
                                                                    apply_close
                                                                    bind_elab1
                                                                     in
                                                                    ([],
                                                                    uu____3022)
                                                                     in
                                                                  {
                                                                    FStar_Syntax_Syntax.monad_m
                                                                    =
                                                                    uu____3012;
                                                                    FStar_Syntax_Syntax.monad_ret
                                                                    =
                                                                    uu____3013;
                                                                    FStar_Syntax_Syntax.monad_bind
                                                                    =
                                                                    uu____3021
                                                                  }  in
                                                                {
                                                                  FStar_Syntax_Syntax.cattributes
                                                                    =
                                                                    (
                                                                    uu___336_2991.FStar_Syntax_Syntax.cattributes);
                                                                  FStar_Syntax_Syntax.mname
                                                                    =
                                                                    (
                                                                    uu___336_2991.FStar_Syntax_Syntax.mname);
                                                                  FStar_Syntax_Syntax.univs
                                                                    =
                                                                    (
                                                                    uu___336_2991.FStar_Syntax_Syntax.univs);
                                                                  FStar_Syntax_Syntax.binders
                                                                    =
                                                                    uu____2992;
                                                                  FStar_Syntax_Syntax.spec
                                                                    =
                                                                    uu____2993;
                                                                  FStar_Syntax_Syntax.signature
                                                                    =
                                                                    uu____3010;
                                                                  FStar_Syntax_Syntax.if_then_else
                                                                    =
                                                                    (
                                                                    uu___336_2991.FStar_Syntax_Syntax.if_then_else);
                                                                  FStar_Syntax_Syntax.ite_wp
                                                                    =
                                                                    (
                                                                    uu___336_2991.FStar_Syntax_Syntax.ite_wp);
                                                                  FStar_Syntax_Syntax.stronger
                                                                    =
                                                                    (
                                                                    uu___336_2991.FStar_Syntax_Syntax.stronger);
                                                                  FStar_Syntax_Syntax.close_wp
                                                                    =
                                                                    (
                                                                    uu___336_2991.FStar_Syntax_Syntax.close_wp);
                                                                  FStar_Syntax_Syntax.trivial
                                                                    =
                                                                    (
                                                                    uu___336_2991.FStar_Syntax_Syntax.trivial);
                                                                  FStar_Syntax_Syntax.repr
                                                                    =
                                                                    uu____3011;
                                                                  FStar_Syntax_Syntax.elaborated
                                                                    =
                                                                    (
                                                                    uu___336_2991.FStar_Syntax_Syntax.elaborated);
                                                                  FStar_Syntax_Syntax.spec_dm4f
                                                                    =
                                                                    (
                                                                    uu___336_2991.FStar_Syntax_Syntax.spec_dm4f);
                                                                  FStar_Syntax_Syntax.interp
                                                                    =
                                                                    (
                                                                    uu___336_2991.FStar_Syntax_Syntax.interp);
                                                                  FStar_Syntax_Syntax.mrelation
                                                                    =
                                                                    (
                                                                    uu___336_2991.FStar_Syntax_Syntax.mrelation);
                                                                  FStar_Syntax_Syntax.actions
                                                                    =
                                                                    actions1;
                                                                  FStar_Syntax_Syntax.eff_attrs
                                                                    =
                                                                    (
                                                                    uu___336_2991.FStar_Syntax_Syntax.eff_attrs)
                                                                }  in
                                                              let uu____3029
                                                                =
                                                                FStar_TypeChecker_DMFF.gen_wps_for_free
                                                                  env1
                                                                  effect_binders1
                                                                  a1 wp_a ed2
                                                                 in
                                                              match uu____3029
                                                              with
                                                              | (sigelts',ed3)
                                                                  ->
                                                                  ((let uu____3047
                                                                    =
                                                                    FStar_TypeChecker_Env.debug
                                                                    env1
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____3047
                                                                    then
                                                                    let uu____3051
                                                                    =
                                                                    FStar_Syntax_Print.eff_decl_to_string
                                                                    ed3  in
                                                                    FStar_Util.print_string
                                                                    uu____3051
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
                                                                    let uu____3070
                                                                    =
                                                                    let uu____3073
                                                                    =
                                                                    let uu____3074
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____3074)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3073
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed3.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____3070;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                    let uu____3081
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3081
                                                                    else
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____3084
                                                                    =
                                                                    let uu____3087
                                                                    =
                                                                    let uu____3090
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                    FStar_List.rev
                                                                    uu____3090
                                                                     in
                                                                    FStar_List.append
                                                                    uu____3087
                                                                    sigelts'
                                                                     in
                                                                    (uu____3084,
                                                                    ed3,
                                                                    lift_from_pure_opt)))))))))))))))))))
  
let tc_eff_decl :
  'Auu____3129 .
    FStar_TypeChecker_Env.env ->
      'Auu____3129 ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun se  ->
      fun ed  ->
        (let uu____3146 =
           FStar_TypeChecker_Env.debug env0 (FStar_Options.Other "ED")  in
         if uu____3146
         then
           let uu____3150 = FStar_Syntax_Print.eff_decl_to_string ed  in
           FStar_Util.print1 "initial eff_decl :\n\t%s\n" uu____3150
         else ());
        (let uu____3155 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____3155 with
         | (open_annotated_univs,annotated_univ_names) ->
             let open_univs n_binders t =
               let uu____3187 =
                 FStar_Syntax_Subst.shift_subst n_binders
                   open_annotated_univs
                  in
               FStar_Syntax_Subst.subst uu____3187 t  in
             let open_univs_binders n_binders bs =
               let uu____3203 =
                 FStar_Syntax_Subst.shift_subst n_binders
                   open_annotated_univs
                  in
               FStar_Syntax_Subst.subst_binders uu____3203 bs  in
             let n_effect_params =
               FStar_List.length ed.FStar_Syntax_Syntax.binders  in
             let signature = ed.FStar_Syntax_Syntax.signature  in
             let uu____3214 =
               let uu____3221 =
                 open_univs_binders Prims.int_zero
                   ed.FStar_Syntax_Syntax.binders
                  in
               let uu____3223 = open_univs n_effect_params signature  in
               FStar_Syntax_Subst.open_term' uu____3221 uu____3223  in
             (match uu____3214 with
              | (effect_params_un,signature_un,opening) ->
                  let env =
                    FStar_TypeChecker_Env.push_univ_vars env0
                      annotated_univ_names
                     in
                  let uu____3228 =
                    FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un
                     in
                  (match uu____3228 with
                   | (effect_params,env1,uu____3237) ->
                       let uu____3238 =
                         FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                           signature_un
                          in
                       (match uu____3238 with
                        | (signature1,uu____3244) ->
                            let ed1 =
                              let uu___375_3246 = ed  in
                              {
                                FStar_Syntax_Syntax.cattributes =
                                  (uu___375_3246.FStar_Syntax_Syntax.cattributes);
                                FStar_Syntax_Syntax.mname =
                                  (uu___375_3246.FStar_Syntax_Syntax.mname);
                                FStar_Syntax_Syntax.univs =
                                  (uu___375_3246.FStar_Syntax_Syntax.univs);
                                FStar_Syntax_Syntax.binders = effect_params;
                                FStar_Syntax_Syntax.spec =
                                  (uu___375_3246.FStar_Syntax_Syntax.spec);
                                FStar_Syntax_Syntax.signature = signature1;
                                FStar_Syntax_Syntax.if_then_else =
                                  (uu___375_3246.FStar_Syntax_Syntax.if_then_else);
                                FStar_Syntax_Syntax.ite_wp =
                                  (uu___375_3246.FStar_Syntax_Syntax.ite_wp);
                                FStar_Syntax_Syntax.stronger =
                                  (uu___375_3246.FStar_Syntax_Syntax.stronger);
                                FStar_Syntax_Syntax.close_wp =
                                  (uu___375_3246.FStar_Syntax_Syntax.close_wp);
                                FStar_Syntax_Syntax.trivial =
                                  (uu___375_3246.FStar_Syntax_Syntax.trivial);
                                FStar_Syntax_Syntax.repr =
                                  (uu___375_3246.FStar_Syntax_Syntax.repr);
                                FStar_Syntax_Syntax.elaborated =
                                  (uu___375_3246.FStar_Syntax_Syntax.elaborated);
                                FStar_Syntax_Syntax.spec_dm4f =
                                  (uu___375_3246.FStar_Syntax_Syntax.spec_dm4f);
                                FStar_Syntax_Syntax.interp =
                                  (uu___375_3246.FStar_Syntax_Syntax.interp);
                                FStar_Syntax_Syntax.mrelation =
                                  (uu___375_3246.FStar_Syntax_Syntax.mrelation);
                                FStar_Syntax_Syntax.actions =
                                  (uu___375_3246.FStar_Syntax_Syntax.actions);
                                FStar_Syntax_Syntax.eff_attrs =
                                  (uu___375_3246.FStar_Syntax_Syntax.eff_attrs)
                              }  in
                            let ed2 =
                              match (effect_params, annotated_univ_names)
                              with
                              | ([],[]) -> ed1
                              | uu____3274 ->
                                  let op uu____3306 =
                                    match uu____3306 with
                                    | (us,t) ->
                                        let n_us = FStar_List.length us  in
                                        let uu____3326 =
                                          let uu____3327 =
                                            FStar_Syntax_Subst.shift_subst
                                              n_us opening
                                             in
                                          let uu____3330 = open_univs n_us t
                                             in
                                          FStar_Syntax_Subst.subst uu____3327
                                            uu____3330
                                           in
                                        (us, uu____3326)
                                     in
                                  let uu___387_3333 = ed1  in
                                  let uu____3334 =
                                    let uu____3335 =
                                      let uu____3336 =
                                        op
                                          ([],
                                            ((ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m))
                                         in
                                      FStar_Pervasives_Native.snd uu____3336
                                       in
                                    let uu____3347 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                       in
                                    let uu____3348 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                       in
                                    {
                                      FStar_Syntax_Syntax.monad_m =
                                        uu____3335;
                                      FStar_Syntax_Syntax.monad_ret =
                                        uu____3347;
                                      FStar_Syntax_Syntax.monad_bind =
                                        uu____3348
                                    }  in
                                  let uu____3349 =
                                    op ed1.FStar_Syntax_Syntax.if_then_else
                                     in
                                  let uu____3350 =
                                    op ed1.FStar_Syntax_Syntax.ite_wp  in
                                  let uu____3351 =
                                    op ed1.FStar_Syntax_Syntax.stronger  in
                                  let uu____3352 =
                                    op ed1.FStar_Syntax_Syntax.close_wp  in
                                  let uu____3353 =
                                    op ed1.FStar_Syntax_Syntax.trivial  in
                                  let uu____3354 =
                                    let uu____3355 =
                                      let uu____3356 =
                                        op
                                          ([],
                                            ((ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m))
                                         in
                                      FStar_Pervasives_Native.snd uu____3356
                                       in
                                    let uu____3367 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                       in
                                    let uu____3368 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                       in
                                    {
                                      FStar_Syntax_Syntax.monad_m =
                                        uu____3355;
                                      FStar_Syntax_Syntax.monad_ret =
                                        uu____3367;
                                      FStar_Syntax_Syntax.monad_bind =
                                        uu____3368
                                    }  in
                                  let uu____3369 =
                                    FStar_List.map
                                      (fun a  ->
                                         let uu___390_3377 = a  in
                                         let uu____3378 =
                                           let uu____3379 =
                                             op
                                               ((a.FStar_Syntax_Syntax.action_univs),
                                                 (a.FStar_Syntax_Syntax.action_defn))
                                              in
                                           FStar_Pervasives_Native.snd
                                             uu____3379
                                            in
                                         let uu____3390 =
                                           let uu____3391 =
                                             op
                                               ((a.FStar_Syntax_Syntax.action_univs),
                                                 (a.FStar_Syntax_Syntax.action_typ))
                                              in
                                           FStar_Pervasives_Native.snd
                                             uu____3391
                                            in
                                         {
                                           FStar_Syntax_Syntax.action_name =
                                             (uu___390_3377.FStar_Syntax_Syntax.action_name);
                                           FStar_Syntax_Syntax.action_unqualified_name
                                             =
                                             (uu___390_3377.FStar_Syntax_Syntax.action_unqualified_name);
                                           FStar_Syntax_Syntax.action_univs =
                                             (uu___390_3377.FStar_Syntax_Syntax.action_univs);
                                           FStar_Syntax_Syntax.action_params
                                             =
                                             (uu___390_3377.FStar_Syntax_Syntax.action_params);
                                           FStar_Syntax_Syntax.action_defn =
                                             uu____3378;
                                           FStar_Syntax_Syntax.action_typ =
                                             uu____3390
                                         }) ed1.FStar_Syntax_Syntax.actions
                                     in
                                  {
                                    FStar_Syntax_Syntax.cattributes =
                                      (uu___387_3333.FStar_Syntax_Syntax.cattributes);
                                    FStar_Syntax_Syntax.mname =
                                      (uu___387_3333.FStar_Syntax_Syntax.mname);
                                    FStar_Syntax_Syntax.univs =
                                      annotated_univ_names;
                                    FStar_Syntax_Syntax.binders =
                                      (uu___387_3333.FStar_Syntax_Syntax.binders);
                                    FStar_Syntax_Syntax.spec = uu____3334;
                                    FStar_Syntax_Syntax.signature =
                                      (uu___387_3333.FStar_Syntax_Syntax.signature);
                                    FStar_Syntax_Syntax.if_then_else =
                                      uu____3349;
                                    FStar_Syntax_Syntax.ite_wp = uu____3350;
                                    FStar_Syntax_Syntax.stronger = uu____3351;
                                    FStar_Syntax_Syntax.close_wp = uu____3352;
                                    FStar_Syntax_Syntax.trivial = uu____3353;
                                    FStar_Syntax_Syntax.repr = uu____3354;
                                    FStar_Syntax_Syntax.elaborated =
                                      (uu___387_3333.FStar_Syntax_Syntax.elaborated);
                                    FStar_Syntax_Syntax.spec_dm4f =
                                      (uu___387_3333.FStar_Syntax_Syntax.spec_dm4f);
                                    FStar_Syntax_Syntax.interp =
                                      (uu___387_3333.FStar_Syntax_Syntax.interp);
                                    FStar_Syntax_Syntax.mrelation =
                                      (uu___387_3333.FStar_Syntax_Syntax.mrelation);
                                    FStar_Syntax_Syntax.actions = uu____3369;
                                    FStar_Syntax_Syntax.eff_attrs =
                                      (uu___387_3333.FStar_Syntax_Syntax.eff_attrs)
                                  }
                               in
                            ((let uu____3403 =
                                FStar_TypeChecker_Env.debug env0
                                  (FStar_Options.Other "ED")
                                 in
                              if uu____3403
                              then
                                let uu____3407 =
                                  FStar_Syntax_Print.eff_decl_to_string ed2
                                   in
                                FStar_Util.print1
                                  "eff_decl after opening:\n\t%s\n"
                                  uu____3407
                              else ());
                             (let wp_with_fresh_result_type env2 mname
                                signature2 =
                                let fail1 t =
                                  let uu____3446 =
                                    FStar_TypeChecker_Err.unexpected_signature_for_monad
                                      env2 mname t
                                     in
                                  let uu____3452 =
                                    FStar_Ident.range_of_lid mname  in
                                  FStar_Errors.raise_error uu____3446
                                    uu____3452
                                   in
                                let uu____3459 =
                                  let uu____3460 =
                                    FStar_Syntax_Subst.compress signature2
                                     in
                                  uu____3460.FStar_Syntax_Syntax.n  in
                                match uu____3459 with
                                | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                    let bs1 =
                                      FStar_Syntax_Subst.open_binders bs  in
                                    (match bs1 with
                                     | (a,uu____3499)::(wp,uu____3501)::[] ->
                                         (a, (wp.FStar_Syntax_Syntax.sort))
                                     | uu____3530 -> fail1 signature2)
                                | uu____3531 -> fail1 signature2  in
                              let uu____3532 =
                                wp_with_fresh_result_type env1
                                  ed2.FStar_Syntax_Syntax.mname signature1
                                 in
                              match uu____3532 with
                              | (a,wp_a) ->
                                  let fresh_effect_signature uu____3556 =
                                    match annotated_univ_names with
                                    | [] ->
                                        let uu____3563 =
                                          FStar_TypeChecker_TcTerm.tc_trivial_guard
                                            env1 signature_un
                                           in
                                        (match uu____3563 with
                                         | (signature2,uu____3575) ->
                                             wp_with_fresh_result_type env1
                                               ed2.FStar_Syntax_Syntax.mname
                                               signature2)
                                    | uu____3576 ->
                                        let uu____3579 =
                                          let uu____3584 =
                                            let uu____3585 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                annotated_univ_names
                                                signature1
                                               in
                                            (annotated_univ_names,
                                              uu____3585)
                                             in
                                          FStar_TypeChecker_Env.inst_tscheme
                                            uu____3584
                                           in
                                        (match uu____3579 with
                                         | (uu____3598,signature2) ->
                                             wp_with_fresh_result_type env1
                                               ed2.FStar_Syntax_Syntax.mname
                                               signature2)
                                     in
                                  let env2 =
                                    let uu____3601 =
                                      FStar_Syntax_Syntax.new_bv
                                        FStar_Pervasives_Native.None
                                        signature1
                                       in
                                    FStar_TypeChecker_Env.push_bv env1
                                      uu____3601
                                     in
                                  ((let uu____3603 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env0)
                                        (FStar_Options.Other "ED")
                                       in
                                    if uu____3603
                                    then
                                      let uu____3608 =
                                        FStar_Syntax_Print.lid_to_string
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      let uu____3610 =
                                        FStar_Syntax_Print.binders_to_string
                                          " " ed2.FStar_Syntax_Syntax.binders
                                         in
                                      let uu____3613 =
                                        FStar_Syntax_Print.term_to_string
                                          signature1
                                         in
                                      let uu____3615 =
                                        let uu____3617 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Print.term_to_string
                                          uu____3617
                                         in
                                      let uu____3618 =
                                        FStar_Syntax_Print.term_to_string
                                          a.FStar_Syntax_Syntax.sort
                                         in
                                      FStar_Util.print5
                                        "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                        uu____3608 uu____3610 uu____3613
                                        uu____3615 uu____3618
                                    else ());
                                   (let check_and_gen' env3 uu____3653 k =
                                      match uu____3653 with
                                      | (us,t) ->
                                          (match annotated_univ_names with
                                           | [] -> check_and_gen env3 t k
                                           | uu____3689::uu____3690 ->
                                               let uu____3693 =
                                                 FStar_Syntax_Subst.subst_tscheme
                                                   open_annotated_univs
                                                   (us, t)
                                                  in
                                               (match uu____3693 with
                                                | (us1,t1) ->
                                                    let uu____3716 =
                                                      FStar_Syntax_Subst.open_univ_vars
                                                        us1 t1
                                                       in
                                                    (match uu____3716 with
                                                     | (us2,t2) ->
                                                         let uu____3731 =
                                                           let uu____3732 =
                                                             FStar_TypeChecker_Env.push_univ_vars
                                                               env3 us2
                                                              in
                                                           tc_check_trivial_guard
                                                             uu____3732 t2 k
                                                            in
                                                         let uu____3733 =
                                                           FStar_Syntax_Subst.close_univ_vars
                                                             us2 t2
                                                            in
                                                         (us2, uu____3733))))
                                       in
                                    let return_wp =
                                      let expected_k =
                                        let uu____3752 =
                                          let uu____3761 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____3768 =
                                            let uu____3777 =
                                              let uu____3784 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____3784
                                               in
                                            [uu____3777]  in
                                          uu____3761 :: uu____3768  in
                                        let uu____3803 =
                                          FStar_Syntax_Syntax.mk_GTotal wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____3752
                                          uu____3803
                                         in
                                      check_and_gen' env2
                                        (ed2.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                        expected_k
                                       in
                                    let bind_wp =
                                      let uu____3807 =
                                        fresh_effect_signature ()  in
                                      match uu____3807 with
                                      | (b,wp_b) ->
                                          let a_wp_b =
                                            let uu____3823 =
                                              let uu____3832 =
                                                let uu____3839 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____3839
                                                 in
                                              [uu____3832]  in
                                            let uu____3852 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_b
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____3823 uu____3852
                                             in
                                          let expected_k =
                                            let uu____3858 =
                                              let uu____3867 =
                                                FStar_Syntax_Syntax.null_binder
                                                  FStar_Syntax_Syntax.t_range
                                                 in
                                              let uu____3874 =
                                                let uu____3883 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____3890 =
                                                  let uu____3899 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____3906 =
                                                    let uu____3915 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_a
                                                       in
                                                    let uu____3922 =
                                                      let uu____3931 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          a_wp_b
                                                         in
                                                      [uu____3931]  in
                                                    uu____3915 :: uu____3922
                                                     in
                                                  uu____3899 :: uu____3906
                                                   in
                                                uu____3883 :: uu____3890  in
                                              uu____3867 :: uu____3874  in
                                            let uu____3974 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_b
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____3858 uu____3974
                                             in
                                          check_and_gen' env2
                                            (ed2.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                            expected_k
                                       in
                                    let mk_simple_repr t =
                                      let uu____3985 =
                                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                          env2
                                          (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                         in
                                      match uu____3985 with
                                      | (repr,uu____3995,uu____3996) ->
                                          let uu____3997 =
                                            let uu____4008 =
                                              FStar_Syntax_Syntax.as_arg t
                                               in
                                            [uu____4008]  in
                                          FStar_Syntax_Util.mk_app repr
                                            uu____3997
                                       in
                                    let interp =
                                      match ed2.FStar_Syntax_Syntax.interp
                                      with
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some interp
                                          ->
                                          let repr_a =
                                            let uu____4042 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            mk_simple_repr uu____4042  in
                                          let expected_k =
                                            let uu____4046 =
                                              let uu____4055 =
                                                FStar_Syntax_Syntax.mk_implicit_binder
                                                  a
                                                 in
                                              let uu____4062 =
                                                let uu____4071 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    repr_a
                                                   in
                                                [uu____4071]  in
                                              uu____4055 :: uu____4062  in
                                            let uu____4096 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4046 uu____4096
                                             in
                                          let uu____4099 =
                                            check_and_gen' env2 interp
                                              expected_k
                                             in
                                          FStar_All.pipe_left
                                            (fun _4102  ->
                                               FStar_Pervasives_Native.Some
                                                 _4102) uu____4099
                                       in
                                    let mrelation =
                                      match ed2.FStar_Syntax_Syntax.mrelation
                                      with
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some
                                          mrelation ->
                                          let uu____4109 =
                                            FStar_Syntax_Util.type_u ()  in
                                          (match uu____4109 with
                                           | (t,uu____4117) ->
                                               let repr_a =
                                                 let uu____4121 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     a
                                                    in
                                                 mk_simple_repr uu____4121
                                                  in
                                               let expected_k =
                                                 let uu____4125 =
                                                   let uu____4134 =
                                                     FStar_Syntax_Syntax.mk_implicit_binder
                                                       a
                                                      in
                                                   let uu____4141 =
                                                     let uu____4150 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         repr_a
                                                        in
                                                     let uu____4157 =
                                                       let uu____4166 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_a
                                                          in
                                                       [uu____4166]  in
                                                     uu____4150 :: uu____4157
                                                      in
                                                   uu____4134 :: uu____4141
                                                    in
                                                 let uu____4197 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____4125 uu____4197
                                                  in
                                               let uu____4200 =
                                                 check_and_gen' env2
                                                   mrelation expected_k
                                                  in
                                               FStar_All.pipe_left
                                                 (fun _4203  ->
                                                    FStar_Pervasives_Native.Some
                                                      _4203) uu____4200)
                                       in
                                    let if_then_else1 =
                                      let p =
                                        let uu____4214 =
                                          let uu____4217 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4217
                                           in
                                        let uu____4218 =
                                          let uu____4219 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4219
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4214
                                          uu____4218
                                         in
                                      let expected_k =
                                        let uu____4231 =
                                          let uu____4240 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4247 =
                                            let uu____4256 =
                                              FStar_Syntax_Syntax.mk_binder p
                                               in
                                            let uu____4263 =
                                              let uu____4272 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              let uu____4279 =
                                                let uu____4288 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____4288]  in
                                              uu____4272 :: uu____4279  in
                                            uu____4256 :: uu____4263  in
                                          uu____4240 :: uu____4247  in
                                        let uu____4325 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4231
                                          uu____4325
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.if_then_else
                                        expected_k
                                       in
                                    let ite_wp =
                                      let expected_k =
                                        let uu____4340 =
                                          let uu____4349 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4356 =
                                            let uu____4365 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____4365]  in
                                          uu____4349 :: uu____4356  in
                                        let uu____4390 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4340
                                          uu____4390
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.ite_wp
                                        expected_k
                                       in
                                    let stronger =
                                      let uu____4394 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____4394 with
                                      | (t,uu____4400) ->
                                          let expected_k =
                                            let uu____4404 =
                                              let uu____4413 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4420 =
                                                let uu____4429 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____4436 =
                                                  let uu____4445 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____4445]  in
                                                uu____4429 :: uu____4436  in
                                              uu____4413 :: uu____4420  in
                                            let uu____4476 =
                                              FStar_Syntax_Syntax.mk_Total t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4404 uu____4476
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.stronger
                                            expected_k
                                       in
                                    let close_wp =
                                      let b =
                                        let uu____4489 =
                                          let uu____4492 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4492
                                           in
                                        let uu____4493 =
                                          let uu____4494 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4494
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4489
                                          uu____4493
                                         in
                                      let b_wp_a =
                                        let uu____4506 =
                                          let uu____4515 =
                                            let uu____4522 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                b
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____4522
                                             in
                                          [uu____4515]  in
                                        let uu____4535 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4506
                                          uu____4535
                                         in
                                      let expected_k =
                                        let uu____4541 =
                                          let uu____4550 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4557 =
                                            let uu____4566 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____4573 =
                                              let uu____4582 =
                                                FStar_Syntax_Syntax.null_binder
                                                  b_wp_a
                                                 in
                                              [uu____4582]  in
                                            uu____4566 :: uu____4573  in
                                          uu____4550 :: uu____4557  in
                                        let uu____4613 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4541
                                          uu____4613
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.close_wp
                                        expected_k
                                       in
                                    let trivial_wp =
                                      let uu____4617 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____4617 with
                                      | (t,uu____4623) ->
                                          let expected_k =
                                            let uu____4627 =
                                              let uu____4636 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4643 =
                                                let uu____4652 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____4652]  in
                                              uu____4636 :: uu____4643  in
                                            let uu____4677 =
                                              FStar_Syntax_Syntax.mk_GTotal t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4627 uu____4677
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.trivial
                                            expected_k
                                       in
                                    let uu____4680 =
                                      if ed2.FStar_Syntax_Syntax.spec_dm4f
                                      then
                                        let repr =
                                          let uu____4706 =
                                            FStar_Syntax_Util.type_u ()  in
                                          match uu____4706 with
                                          | (t,uu____4712) ->
                                              let expected_k =
                                                let uu____4716 =
                                                  let uu____4725 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____4732 =
                                                    let uu____4741 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_a
                                                       in
                                                    [uu____4741]  in
                                                  uu____4725 :: uu____4732
                                                   in
                                                let uu____4766 =
                                                  FStar_Syntax_Syntax.mk_GTotal
                                                    t
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____4716 uu____4766
                                                 in
                                              ((let uu____4770 =
                                                  FStar_TypeChecker_Env.debug
                                                    env2
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____4770
                                                then
                                                  let uu____4774 =
                                                    FStar_Syntax_Print.term_to_string
                                                      (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                                     in
                                                  let uu____4776 =
                                                    FStar_Syntax_Print.term_to_string
                                                      expected_k
                                                     in
                                                  FStar_Util.print2
                                                    "About to check repr=%s\nat type %s\n"
                                                    uu____4774 uu____4776
                                                else ());
                                               tc_check_trivial_guard env2
                                                 (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                                 expected_k)
                                           in
                                        let mk_repr' t wp =
                                          let repr1 =
                                            FStar_TypeChecker_Normalize.normalize
                                              [FStar_TypeChecker_Env.EraseUniverses;
                                              FStar_TypeChecker_Env.AllowUnboundUniverses]
                                              env2 repr
                                             in
                                          let uu____4795 =
                                            let uu____4802 =
                                              let uu____4803 =
                                                let uu____4820 =
                                                  let uu____4831 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      t
                                                     in
                                                  let uu____4840 =
                                                    let uu____4851 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        wp
                                                       in
                                                    [uu____4851]  in
                                                  uu____4831 :: uu____4840
                                                   in
                                                (repr1, uu____4820)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____4803
                                               in
                                            FStar_Syntax_Syntax.mk uu____4802
                                             in
                                          uu____4795
                                            FStar_Pervasives_Native.None
                                            FStar_Range.dummyRange
                                           in
                                        let mk_repr a1 wp =
                                          let uu____4909 =
                                            FStar_Syntax_Syntax.bv_to_name a1
                                             in
                                          mk_repr' uu____4909 wp  in
                                        let destruct_repr t =
                                          let uu____4924 =
                                            let uu____4925 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____4925.FStar_Syntax_Syntax.n
                                             in
                                          match uu____4924 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____4936,(t1,uu____4938)::
                                               (wp,uu____4940)::[])
                                              -> (t1, wp)
                                          | uu____4999 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let bind_repr =
                                          let r =
                                            let uu____5011 =
                                              FStar_Syntax_Syntax.lid_as_fv
                                                FStar_Parser_Const.range_0
                                                FStar_Syntax_Syntax.delta_constant
                                                FStar_Pervasives_Native.None
                                               in
                                            FStar_All.pipe_right uu____5011
                                              FStar_Syntax_Syntax.fv_to_tm
                                             in
                                          let uu____5012 =
                                            fresh_effect_signature ()  in
                                          match uu____5012 with
                                          | (b,wp_b) ->
                                              let a_wp_b =
                                                let uu____5028 =
                                                  let uu____5037 =
                                                    let uu____5044 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        a
                                                       in
                                                    FStar_Syntax_Syntax.null_binder
                                                      uu____5044
                                                     in
                                                  [uu____5037]  in
                                                let uu____5057 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    wp_b
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____5028 uu____5057
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
                                                let uu____5065 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____5065
                                                 in
                                              let wp_g_x =
                                                let uu____5070 =
                                                  let uu____5075 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      wp_g
                                                     in
                                                  let uu____5076 =
                                                    let uu____5077 =
                                                      let uu____5086 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x_a
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.as_arg
                                                        uu____5086
                                                       in
                                                    [uu____5077]  in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____5075 uu____5076
                                                   in
                                                uu____5070
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____5117 =
                                                    let uu____5122 =
                                                      let uu____5123 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          bind_wp
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____5123
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    let uu____5132 =
                                                      let uu____5133 =
                                                        let uu____5136 =
                                                          let uu____5139 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          let uu____5140 =
                                                            let uu____5143 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                b
                                                               in
                                                            let uu____5144 =
                                                              let uu____5147
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_f
                                                                 in
                                                              let uu____5148
                                                                =
                                                                let uu____5151
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g
                                                                   in
                                                                [uu____5151]
                                                                 in
                                                              uu____5147 ::
                                                                uu____5148
                                                               in
                                                            uu____5143 ::
                                                              uu____5144
                                                             in
                                                          uu____5139 ::
                                                            uu____5140
                                                           in
                                                        r :: uu____5136  in
                                                      FStar_List.map
                                                        FStar_Syntax_Syntax.as_arg
                                                        uu____5133
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____5122 uu____5132
                                                     in
                                                  uu____5117
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr b wp  in
                                              let maybe_range_arg =
                                                let uu____5169 =
                                                  FStar_Util.for_some
                                                    (FStar_Syntax_Util.attr_eq
                                                       FStar_Syntax_Util.dm4f_bind_range_attr)
                                                    ed2.FStar_Syntax_Syntax.eff_attrs
                                                   in
                                                if uu____5169
                                                then
                                                  let uu____5180 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      FStar_Syntax_Syntax.t_range
                                                     in
                                                  let uu____5187 =
                                                    let uu____5196 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        FStar_Syntax_Syntax.t_range
                                                       in
                                                    [uu____5196]  in
                                                  uu____5180 :: uu____5187
                                                else []  in
                                              let expected_k =
                                                let uu____5232 =
                                                  let uu____5241 =
                                                    let uu____5250 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        a
                                                       in
                                                    let uu____5257 =
                                                      let uu____5266 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          b
                                                         in
                                                      [uu____5266]  in
                                                    uu____5250 :: uu____5257
                                                     in
                                                  let uu____5291 =
                                                    let uu____5300 =
                                                      let uu____5309 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          wp_f
                                                         in
                                                      let uu____5316 =
                                                        let uu____5325 =
                                                          let uu____5332 =
                                                            let uu____5333 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            mk_repr a
                                                              uu____5333
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____5332
                                                           in
                                                        let uu____5334 =
                                                          let uu____5343 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              wp_g
                                                             in
                                                          let uu____5350 =
                                                            let uu____5359 =
                                                              let uu____5366
                                                                =
                                                                let uu____5367
                                                                  =
                                                                  let uu____5376
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                  [uu____5376]
                                                                   in
                                                                let uu____5395
                                                                  =
                                                                  let uu____5398
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____5398
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  uu____5367
                                                                  uu____5395
                                                                 in
                                                              FStar_Syntax_Syntax.null_binder
                                                                uu____5366
                                                               in
                                                            [uu____5359]  in
                                                          uu____5343 ::
                                                            uu____5350
                                                           in
                                                        uu____5325 ::
                                                          uu____5334
                                                         in
                                                      uu____5309 ::
                                                        uu____5316
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____5300
                                                     in
                                                  FStar_List.append
                                                    uu____5241 uu____5291
                                                   in
                                                let uu____5443 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____5232 uu____5443
                                                 in
                                              ((let uu____5447 =
                                                  FStar_TypeChecker_Env.debug
                                                    env2
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____5447
                                                then
                                                  let uu____5451 =
                                                    FStar_Syntax_Print.term_to_string
                                                      expected_k
                                                     in
                                                  FStar_Util.print1
                                                    "About to check expected_k %s\n"
                                                    uu____5451
                                                else ());
                                               (let uu____5456 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env2 expected_k
                                                   in
                                                match uu____5456 with
                                                | (expected_k1,uu____5464,uu____5465)
                                                    ->
                                                    ((let uu____5467 =
                                                        FStar_TypeChecker_Env.debug
                                                          env2
                                                          (FStar_Options.Other
                                                             "ED")
                                                         in
                                                      if uu____5467
                                                      then
                                                        let uu____5471 =
                                                          FStar_Syntax_Print.term_to_string
                                                            (FStar_Pervasives_Native.snd
                                                               (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind)
                                                           in
                                                        let uu____5477 =
                                                          FStar_Syntax_Print.term_to_string
                                                            expected_k1
                                                           in
                                                        FStar_Util.print2
                                                          "About to check bind=%s\n\n, at type %s\n"
                                                          uu____5471
                                                          uu____5477
                                                      else ());
                                                     (let env3 =
                                                        FStar_TypeChecker_Env.set_range
                                                          env2
                                                          (FStar_Pervasives_Native.snd
                                                             (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind).FStar_Syntax_Syntax.pos
                                                         in
                                                      let env4 =
                                                        let uu___547_5488 =
                                                          env3  in
                                                        {
                                                          FStar_TypeChecker_Env.solver
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.solver);
                                                          FStar_TypeChecker_Env.range
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.range);
                                                          FStar_TypeChecker_Env.curmodule
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.curmodule);
                                                          FStar_TypeChecker_Env.gamma
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.gamma);
                                                          FStar_TypeChecker_Env.gamma_sig
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.gamma_sig);
                                                          FStar_TypeChecker_Env.gamma_cache
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.gamma_cache);
                                                          FStar_TypeChecker_Env.modules
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.modules);
                                                          FStar_TypeChecker_Env.expected_typ
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.expected_typ);
                                                          FStar_TypeChecker_Env.sigtab
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.sigtab);
                                                          FStar_TypeChecker_Env.attrtab
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.attrtab);
                                                          FStar_TypeChecker_Env.is_pattern
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.is_pattern);
                                                          FStar_TypeChecker_Env.instantiate_imp
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.instantiate_imp);
                                                          FStar_TypeChecker_Env.effects
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.effects);
                                                          FStar_TypeChecker_Env.generalize
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.generalize);
                                                          FStar_TypeChecker_Env.letrecs
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.letrecs);
                                                          FStar_TypeChecker_Env.top_level
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.top_level);
                                                          FStar_TypeChecker_Env.check_uvars
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.check_uvars);
                                                          FStar_TypeChecker_Env.use_eq
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.use_eq);
                                                          FStar_TypeChecker_Env.is_iface
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.is_iface);
                                                          FStar_TypeChecker_Env.admit
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.admit);
                                                          FStar_TypeChecker_Env.lax
                                                            = true;
                                                          FStar_TypeChecker_Env.lax_universes
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.lax_universes);
                                                          FStar_TypeChecker_Env.phase1
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.phase1);
                                                          FStar_TypeChecker_Env.failhard
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.failhard);
                                                          FStar_TypeChecker_Env.nosynth
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.nosynth);
                                                          FStar_TypeChecker_Env.uvar_subtyping
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.uvar_subtyping);
                                                          FStar_TypeChecker_Env.tc_term
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.tc_term);
                                                          FStar_TypeChecker_Env.type_of
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.type_of);
                                                          FStar_TypeChecker_Env.universe_of
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.universe_of);
                                                          FStar_TypeChecker_Env.check_type_of
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.check_type_of);
                                                          FStar_TypeChecker_Env.use_bv_sorts
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.use_bv_sorts);
                                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                          FStar_TypeChecker_Env.normalized_eff_names
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.normalized_eff_names);
                                                          FStar_TypeChecker_Env.fv_delta_depths
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.fv_delta_depths);
                                                          FStar_TypeChecker_Env.proof_ns
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.proof_ns);
                                                          FStar_TypeChecker_Env.synth_hook
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.synth_hook);
                                                          FStar_TypeChecker_Env.splice
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.splice);
                                                          FStar_TypeChecker_Env.postprocess
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.postprocess);
                                                          FStar_TypeChecker_Env.is_native_tactic
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.is_native_tactic);
                                                          FStar_TypeChecker_Env.identifier_info
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.identifier_info);
                                                          FStar_TypeChecker_Env.tc_hooks
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.tc_hooks);
                                                          FStar_TypeChecker_Env.dsenv
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.dsenv);
                                                          FStar_TypeChecker_Env.nbe
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.nbe);
                                                          FStar_TypeChecker_Env.strict_args_tab
                                                            =
                                                            (uu___547_5488.FStar_TypeChecker_Env.strict_args_tab)
                                                        }  in
                                                      let br =
                                                        check_and_gen' env4
                                                          (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                                          expected_k1
                                                         in
                                                      (let uu____5500 =
                                                         FStar_TypeChecker_Env.debug
                                                           env4
                                                           (FStar_Options.Other
                                                              "ED")
                                                          in
                                                       if uu____5500
                                                       then
                                                         let uu____5504 =
                                                           FStar_Syntax_Print.tscheme_to_string
                                                             br
                                                            in
                                                         let uu____5506 =
                                                           FStar_Syntax_Print.term_to_string
                                                             expected_k1
                                                            in
                                                         FStar_Util.print2
                                                           "After checking bind_repr is %s\nexpected_k is %s\n"
                                                           uu____5504
                                                           uu____5506
                                                       else ());
                                                      br))))
                                           in
                                        let return_repr =
                                          let x_a =
                                            let uu____5513 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.gen_bv "x_a"
                                              FStar_Pervasives_Native.None
                                              uu____5513
                                             in
                                          let res =
                                            let wp =
                                              let uu____5521 =
                                                let uu____5526 =
                                                  let uu____5527 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      return_wp
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____5527
                                                    FStar_Pervasives_Native.snd
                                                   in
                                                let uu____5536 =
                                                  let uu____5537 =
                                                    let uu____5540 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        a
                                                       in
                                                    let uu____5541 =
                                                      let uu____5544 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x_a
                                                         in
                                                      [uu____5544]  in
                                                    uu____5540 :: uu____5541
                                                     in
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.as_arg
                                                    uu____5537
                                                   in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____5526 uu____5536
                                                 in
                                              uu____5521
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            mk_repr a wp  in
                                          let expected_k =
                                            let uu____5556 =
                                              let uu____5565 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____5572 =
                                                let uu____5581 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    x_a
                                                   in
                                                [uu____5581]  in
                                              uu____5565 :: uu____5572  in
                                            let uu____5606 =
                                              FStar_Syntax_Syntax.mk_Total
                                                res
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____5556 uu____5606
                                             in
                                          let uu____5609 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k
                                             in
                                          match uu____5609 with
                                          | (expected_k1,uu____5617,uu____5618)
                                              ->
                                              let env3 =
                                                FStar_TypeChecker_Env.set_range
                                                  env2
                                                  (FStar_Pervasives_Native.snd
                                                     (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret).FStar_Syntax_Syntax.pos
                                                 in
                                              let uu____5624 =
                                                check_and_gen' env3
                                                  (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                                  expected_k1
                                                 in
                                              (match uu____5624 with
                                               | (univs1,repr1) ->
                                                   (match univs1 with
                                                    | [] -> ([], repr1)
                                                    | uu____5647 ->
                                                        FStar_Errors.raise_error
                                                          (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                            "Unexpected universe-polymorphic return for effect")
                                                          repr1.FStar_Syntax_Syntax.pos))
                                           in
                                        let actions =
                                          let check_action act =
                                            let uu____5662 =
                                              if
                                                act.FStar_Syntax_Syntax.action_univs
                                                  = []
                                              then (env2, act)
                                              else
                                                (let uu____5676 =
                                                   FStar_Syntax_Subst.univ_var_opening
                                                     act.FStar_Syntax_Syntax.action_univs
                                                    in
                                                 match uu____5676 with
                                                 | (usubst,uvs) ->
                                                     let uu____5699 =
                                                       FStar_TypeChecker_Env.push_univ_vars
                                                         env2 uvs
                                                        in
                                                     let uu____5700 =
                                                       let uu___578_5701 =
                                                         act  in
                                                       let uu____5702 =
                                                         FStar_Syntax_Subst.subst_binders
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_params
                                                          in
                                                       let uu____5703 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____5704 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___578_5701.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___578_5701.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = uvs;
                                                         FStar_Syntax_Syntax.action_params
                                                           = uu____5702;
                                                         FStar_Syntax_Syntax.action_defn
                                                           = uu____5703;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____5704
                                                       }  in
                                                     (uu____5699, uu____5700))
                                               in
                                            match uu____5662 with
                                            | (env3,act1) ->
                                                let act_typ =
                                                  let uu____5708 =
                                                    let uu____5709 =
                                                      FStar_Syntax_Subst.compress
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                       in
                                                    uu____5709.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____5708 with
                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                      (bs,c) ->
                                                      let c1 =
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                          c
                                                         in
                                                      let uu____5735 =
                                                        FStar_Ident.lid_equals
                                                          c1.FStar_Syntax_Syntax.effect_name
                                                          ed2.FStar_Syntax_Syntax.mname
                                                         in
                                                      if uu____5735
                                                      then
                                                        let uu____5738 =
                                                          let uu____5741 =
                                                            let uu____5742 =
                                                              let uu____5743
                                                                =
                                                                FStar_List.hd
                                                                  c1.FStar_Syntax_Syntax.effect_args
                                                                 in
                                                              FStar_Pervasives_Native.fst
                                                                uu____5743
                                                               in
                                                            mk_repr'
                                                              c1.FStar_Syntax_Syntax.result_typ
                                                              uu____5742
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total
                                                            uu____5741
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          bs uu____5738
                                                      else
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                  | uu____5766 ->
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                   in
                                                let uu____5767 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env3 act_typ
                                                   in
                                                (match uu____5767 with
                                                 | (act_typ1,uu____5775,g_t)
                                                     ->
                                                     let env' =
                                                       let uu___595_5778 =
                                                         FStar_TypeChecker_Env.set_expected_typ
                                                           env3 act_typ1
                                                          in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.is_pattern
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.is_pattern);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           = false;
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.lax);
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.nbe);
                                                         FStar_TypeChecker_Env.strict_args_tab
                                                           =
                                                           (uu___595_5778.FStar_TypeChecker_Env.strict_args_tab)
                                                       }  in
                                                     ((let uu____5781 =
                                                         FStar_TypeChecker_Env.debug
                                                           env3
                                                           (FStar_Options.Other
                                                              "ED")
                                                          in
                                                       if uu____5781
                                                       then
                                                         let uu____5785 =
                                                           FStar_Ident.text_of_lid
                                                             act1.FStar_Syntax_Syntax.action_name
                                                            in
                                                         let uu____5787 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____5789 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act_typ1
                                                            in
                                                         FStar_Util.print3
                                                           "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                           uu____5785
                                                           uu____5787
                                                           uu____5789
                                                       else ());
                                                      (let uu____5794 =
                                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                           env'
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       match uu____5794 with
                                                       | (act_defn,uu____5802,g_a)
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
                                                           let uu____5806 =
                                                             let act_typ3 =
                                                               FStar_Syntax_Subst.compress
                                                                 act_typ2
                                                                in
                                                             match act_typ3.FStar_Syntax_Syntax.n
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____5842
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c
                                                                    in
                                                                 (match uu____5842
                                                                  with
                                                                  | (bs1,uu____5854)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____5861
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____5861
                                                                     in
                                                                    let uu____5864
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____5864
                                                                    with
                                                                    | 
                                                                    (k1,uu____5878,g)
                                                                    ->
                                                                    (k1, g)))
                                                             | uu____5882 ->
                                                                 let uu____5883
                                                                   =
                                                                   let uu____5889
                                                                    =
                                                                    let uu____5891
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____5893
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____5891
                                                                    uu____5893
                                                                     in
                                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____5889)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____5883
                                                                   act_defn1.FStar_Syntax_Syntax.pos
                                                              in
                                                           (match uu____5806
                                                            with
                                                            | (expected_k,g_k)
                                                                ->
                                                                let g =
                                                                  FStar_TypeChecker_Rel.teq
                                                                    env3
                                                                    act_typ2
                                                                    expected_k
                                                                   in
                                                                ((let uu____5911
                                                                    =
                                                                    let uu____5912
                                                                    =
                                                                    let uu____5913
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____5913
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____5912
                                                                     in
                                                                  FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env3
                                                                    uu____5911);
                                                                 (let act_typ3
                                                                    =
                                                                    let uu____5915
                                                                    =
                                                                    let uu____5916
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____5916.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5915
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____5941
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____5941
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____5948
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____5948
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____5968
                                                                    =
                                                                    let uu____5969
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____5969]
                                                                     in
                                                                    let uu____5970
                                                                    =
                                                                    let uu____5981
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____5981]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____5968;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____5970;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____6006
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____6006))
                                                                    | 
                                                                    uu____6009
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                  let uu____6011
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env3
                                                                    act_defn1
                                                                    else
                                                                    (let uu____6033
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____6033))
                                                                     in
                                                                  match uu____6011
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
                                                                    let uu___645_6052
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___645_6052.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___645_6052.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___645_6052.FStar_Syntax_Syntax.action_params);
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
                                        (repr, bind_repr, return_repr,
                                          actions)
                                      else
                                        if
                                          (let uu____6061 =
                                             FStar_Syntax_Util.is_unknown
                                               (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                              in
                                           Prims.op_Negation uu____6061)
                                        then
                                          (let repr =
                                             let uu____6064 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             match uu____6064 with
                                             | (t,uu____6070) ->
                                                 let expected_k =
                                                   let uu____6074 =
                                                     let uu____6083 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     [uu____6083]  in
                                                   let uu____6102 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6074 uu____6102
                                                    in
                                                 ((let uu____6106 =
                                                     FStar_TypeChecker_Env.debug
                                                       env2
                                                       (FStar_Options.Other
                                                          "ED")
                                                      in
                                                   if uu____6106
                                                   then
                                                     let uu____6110 =
                                                       FStar_Syntax_Print.term_to_string
                                                         (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                                        in
                                                     let uu____6112 =
                                                       FStar_Syntax_Print.term_to_string
                                                         expected_k
                                                        in
                                                     FStar_Util.print2
                                                       "About to check repr=%s\nat type %s\n"
                                                       uu____6110 uu____6112
                                                   else ());
                                                  tc_check_trivial_guard env2
                                                    (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                                    expected_k)
                                              in
                                           let mk_repr' t =
                                             let repr1 =
                                               FStar_TypeChecker_Normalize.normalize
                                                 [FStar_TypeChecker_Env.EraseUniverses;
                                                 FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                 env2 repr
                                                in
                                             let uu____6126 =
                                               let uu____6133 =
                                                 let uu____6134 =
                                                   let uu____6151 =
                                                     let uu____6162 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____6162]  in
                                                   (repr1, uu____6151)  in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6134
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____6133
                                                in
                                             uu____6126
                                               FStar_Pervasives_Native.None
                                               FStar_Range.dummyRange
                                              in
                                           let mk_repr a1 =
                                             let uu____6207 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a1
                                                in
                                             mk_repr' uu____6207  in
                                           let destruct_repr t =
                                             let uu____6222 =
                                               let uu____6223 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____6223.FStar_Syntax_Syntax.n
                                                in
                                             match uu____6222 with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____6234,(t1,uu____6236)::
                                                  (wp,uu____6238)::[])
                                                 -> (t1, wp)
                                             | uu____6297 ->
                                                 failwith
                                                   "Unexpected repr type"
                                              in
                                           let bind_repr =
                                             let r =
                                               let uu____6309 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_0
                                                   FStar_Syntax_Syntax.delta_constant
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_All.pipe_right
                                                 uu____6309
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                in
                                             let uu____6310 =
                                               fresh_effect_signature ()  in
                                             match uu____6310 with
                                             | (b,wp_b) ->
                                                 let x_a =
                                                   let uu____6324 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "x_a"
                                                     FStar_Pervasives_Native.None
                                                     uu____6324
                                                    in
                                                 let expected_k =
                                                   let uu____6329 =
                                                     let uu____6338 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6345 =
                                                       let uu____6354 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           b
                                                          in
                                                       let uu____6361 =
                                                         let uu____6370 =
                                                           let uu____6377 =
                                                             mk_repr a  in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____6377
                                                            in
                                                         let uu____6378 =
                                                           let uu____6387 =
                                                             let uu____6394 =
                                                               let uu____6395
                                                                 =
                                                                 let uu____6404
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_binder
                                                                    x_a
                                                                    in
                                                                 [uu____6404]
                                                                  in
                                                               let uu____6423
                                                                 =
                                                                 let uu____6426
                                                                   =
                                                                   mk_repr b
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Syntax.mk_Total
                                                                   uu____6426
                                                                  in
                                                               FStar_Syntax_Util.arrow
                                                                 uu____6395
                                                                 uu____6423
                                                                in
                                                             FStar_Syntax_Syntax.null_binder
                                                               uu____6394
                                                              in
                                                           [uu____6387]  in
                                                         uu____6370 ::
                                                           uu____6378
                                                          in
                                                       uu____6354 ::
                                                         uu____6361
                                                        in
                                                     uu____6338 :: uu____6345
                                                      in
                                                   let uu____6459 =
                                                     let uu____6462 =
                                                       mk_repr b  in
                                                     FStar_Syntax_Syntax.mk_Total
                                                       uu____6462
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6329 uu____6459
                                                    in
                                                 ((let uu____6464 =
                                                     FStar_TypeChecker_Env.debug
                                                       env2
                                                       (FStar_Options.Other
                                                          "ED")
                                                      in
                                                   if uu____6464
                                                   then
                                                     let uu____6468 =
                                                       FStar_Syntax_Print.term_to_string
                                                         expected_k
                                                        in
                                                     FStar_Util.print1
                                                       "About to check expected_k %s\n"
                                                       uu____6468
                                                   else ());
                                                  (let uu____6473 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env2 expected_k
                                                      in
                                                   match uu____6473 with
                                                   | (expected_k1,uu____6481,uu____6482)
                                                       ->
                                                       ((let uu____6484 =
                                                           FStar_TypeChecker_Env.debug
                                                             env2
                                                             (FStar_Options.Other
                                                                "ED")
                                                            in
                                                         if uu____6484
                                                         then
                                                           let uu____6488 =
                                                             FStar_Syntax_Print.term_to_string
                                                               (FStar_Pervasives_Native.snd
                                                                  (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind)
                                                              in
                                                           let uu____6494 =
                                                             FStar_Syntax_Print.term_to_string
                                                               expected_k1
                                                              in
                                                           FStar_Util.print2
                                                             "About to check bind=%s\n\n, at type %s\n"
                                                             uu____6488
                                                             uu____6494
                                                         else ());
                                                        (let env3 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env2
                                                             (FStar_Pervasives_Native.snd
                                                                (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind).FStar_Syntax_Syntax.pos
                                                            in
                                                         let br =
                                                           check_and_gen'
                                                             env3
                                                             (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                                             expected_k1
                                                            in
                                                         (let uu____6514 =
                                                            FStar_TypeChecker_Env.debug
                                                              env3
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____6514
                                                          then
                                                            let uu____6518 =
                                                              FStar_Syntax_Print.tscheme_to_string
                                                                br
                                                               in
                                                            let uu____6520 =
                                                              FStar_Syntax_Print.term_to_string
                                                                expected_k1
                                                               in
                                                            FStar_Util.print2
                                                              "After checking bind_repr is %s\nexpected_k is %s\n"
                                                              uu____6518
                                                              uu____6520
                                                          else ());
                                                         br))))
                                              in
                                           let return_repr =
                                             let x_a =
                                               let uu____6527 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   a
                                                  in
                                               FStar_Syntax_Syntax.gen_bv
                                                 "x_a"
                                                 FStar_Pervasives_Native.None
                                                 uu____6527
                                                in
                                             let res = mk_repr a  in
                                             let expected_k =
                                               let uu____6535 =
                                                 let uu____6544 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     a
                                                    in
                                                 let uu____6551 =
                                                   let uu____6560 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       x_a
                                                      in
                                                   [uu____6560]  in
                                                 uu____6544 :: uu____6551  in
                                               let uu____6585 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   res
                                                  in
                                               FStar_Syntax_Util.arrow
                                                 uu____6535 uu____6585
                                                in
                                             let uu____6588 =
                                               FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                 env2 expected_k
                                                in
                                             match uu____6588 with
                                             | (expected_k1,uu____6596,uu____6597)
                                                 ->
                                                 let env3 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env2
                                                     (FStar_Pervasives_Native.snd
                                                        (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret).FStar_Syntax_Syntax.pos
                                                    in
                                                 let uu____6603 =
                                                   check_and_gen' env3
                                                     (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                                     expected_k1
                                                    in
                                                 (match uu____6603 with
                                                  | (univs1,repr1) ->
                                                      (match univs1 with
                                                       | [] -> ([], repr1)
                                                       | uu____6626 ->
                                                           FStar_Errors.raise_error
                                                             (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                               "Unexpected universe-polymorphic return for effect")
                                                             repr1.FStar_Syntax_Syntax.pos))
                                              in
                                           (repr, bind_repr, return_repr,
                                             (ed2.FStar_Syntax_Syntax.actions)))
                                        else
                                          (((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m),
                                            ((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind),
                                            ((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret),
                                            (ed2.FStar_Syntax_Syntax.actions))
                                       in
                                    match uu____4680 with
                                    | (repr,bind_repr,return_repr,actions) ->
                                        let t0 =
                                          let uu____6654 =
                                            FStar_Syntax_Syntax.mk_Total
                                              signature1
                                             in
                                          FStar_Syntax_Util.arrow
                                            ed2.FStar_Syntax_Syntax.binders
                                            uu____6654
                                           in
                                        let uu____6657 =
                                          let uu____6662 =
                                            FStar_TypeChecker_Util.generalize_universes
                                              env0 t0
                                             in
                                          match uu____6662 with
                                          | (gen_univs,t) ->
                                              (match annotated_univ_names
                                               with
                                               | [] -> (gen_univs, t)
                                               | uu____6681 ->
                                                   let uu____6684 =
                                                     ((FStar_List.length
                                                         gen_univs)
                                                        =
                                                        (FStar_List.length
                                                           annotated_univ_names))
                                                       &&
                                                       (FStar_List.forall2
                                                          (fun u1  ->
                                                             fun u2  ->
                                                               let uu____6691
                                                                 =
                                                                 FStar_Syntax_Syntax.order_univ_name
                                                                   u1 u2
                                                                  in
                                                               uu____6691 =
                                                                 Prims.int_zero)
                                                          gen_univs
                                                          annotated_univ_names)
                                                      in
                                                   if uu____6684
                                                   then (gen_univs, t)
                                                   else
                                                     (let uu____6702 =
                                                        let uu____6708 =
                                                          let uu____6710 =
                                                            FStar_Util.string_of_int
                                                              (FStar_List.length
                                                                 annotated_univ_names)
                                                             in
                                                          let uu____6712 =
                                                            FStar_Util.string_of_int
                                                              (FStar_List.length
                                                                 gen_univs)
                                                             in
                                                          FStar_Util.format2
                                                            "Expected an effect definition with %s universes; but found %s"
                                                            uu____6710
                                                            uu____6712
                                                           in
                                                        (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                          uu____6708)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____6702
                                                        signature1.FStar_Syntax_Syntax.pos))
                                           in
                                        (match uu____6657 with
                                         | (univs1,t) ->
                                             let signature2 =
                                               let uu____6723 =
                                                 let uu____6736 =
                                                   let uu____6737 =
                                                     FStar_Syntax_Subst.compress
                                                       t
                                                      in
                                                   uu____6737.FStar_Syntax_Syntax.n
                                                    in
                                                 (effect_params, uu____6736)
                                                  in
                                               match uu____6723 with
                                               | ([],uu____6748) -> t
                                               | (uu____6763,FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____6764,c)) ->
                                                   FStar_Syntax_Util.comp_result
                                                     c
                                               | uu____6802 ->
                                                   failwith
                                                     "Impossible : t is an arrow"
                                                in
                                             let close1 n1 ts =
                                               let ts1 =
                                                 let uu____6830 =
                                                   FStar_Syntax_Subst.close_tscheme
                                                     effect_params ts
                                                    in
                                                 FStar_Syntax_Subst.close_univ_vars_tscheme
                                                   univs1 uu____6830
                                                  in
                                               let m =
                                                 FStar_List.length
                                                   (FStar_Pervasives_Native.fst
                                                      ts1)
                                                  in
                                               (let uu____6837 =
                                                  ((n1 >= Prims.int_zero) &&
                                                     (let uu____6841 =
                                                        FStar_Syntax_Util.is_unknown
                                                          (FStar_Pervasives_Native.snd
                                                             ts1)
                                                         in
                                                      Prims.op_Negation
                                                        uu____6841))
                                                    && (m <> n1)
                                                   in
                                                if uu____6837
                                                then
                                                  let err_msg uu____6855 =
                                                    let error =
                                                      if m < n1
                                                      then
                                                        "not universe-polymorphic enough"
                                                      else
                                                        "too universe-polymorphic"
                                                       in
                                                    let uu____6864 =
                                                      FStar_Util.string_of_int
                                                        m
                                                       in
                                                    let uu____6866 =
                                                      FStar_Util.string_of_int
                                                        n1
                                                       in
                                                    let uu____6868 =
                                                      FStar_Syntax_Print.tscheme_to_string
                                                        ts1
                                                       in
                                                    FStar_Util.format4
                                                      "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                      error uu____6864
                                                      uu____6866 uu____6868
                                                     in
                                                  let uu____6871 =
                                                    let uu____6877 =
                                                      err_msg ()  in
                                                    (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                      uu____6877)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____6871
                                                    (FStar_Pervasives_Native.snd
                                                       ts1).FStar_Syntax_Syntax.pos
                                                else ());
                                               ts1  in
                                             let close_action act =
                                               let uu____6892 =
                                                 close1 (~- Prims.int_one)
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               match uu____6892 with
                                               | (univs2,defn) ->
                                                   let uu____6908 =
                                                     close1
                                                       (~- Prims.int_one)
                                                       ((act.FStar_Syntax_Syntax.action_univs),
                                                         (act.FStar_Syntax_Syntax.action_typ))
                                                      in
                                                   (match uu____6908 with
                                                    | (univs',typ) ->
                                                        let uu___756_6925 =
                                                          act  in
                                                        {
                                                          FStar_Syntax_Syntax.action_name
                                                            =
                                                            (uu___756_6925.FStar_Syntax_Syntax.action_name);
                                                          FStar_Syntax_Syntax.action_unqualified_name
                                                            =
                                                            (uu___756_6925.FStar_Syntax_Syntax.action_unqualified_name);
                                                          FStar_Syntax_Syntax.action_univs
                                                            = univs2;
                                                          FStar_Syntax_Syntax.action_params
                                                            =
                                                            (uu___756_6925.FStar_Syntax_Syntax.action_params);
                                                          FStar_Syntax_Syntax.action_defn
                                                            = defn;
                                                          FStar_Syntax_Syntax.action_typ
                                                            = typ
                                                        })
                                                in
                                             let ed3 =
                                               let uu___759_6928 = ed2  in
                                               let uu____6929 =
                                                 let uu____6930 =
                                                   close1 Prims.int_zero
                                                     return_wp
                                                    in
                                                 let uu____6932 =
                                                   close1 Prims.int_one
                                                     bind_wp
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.monad_m
                                                     =
                                                     FStar_Syntax_Syntax.tun;
                                                   FStar_Syntax_Syntax.monad_ret
                                                     = uu____6930;
                                                   FStar_Syntax_Syntax.monad_bind
                                                     = uu____6932
                                                 }  in
                                               let uu____6934 =
                                                 close1 Prims.int_zero
                                                   if_then_else1
                                                  in
                                               let uu____6936 =
                                                 close1 Prims.int_zero ite_wp
                                                  in
                                               let uu____6938 =
                                                 close1 Prims.int_zero
                                                   stronger
                                                  in
                                               let uu____6940 =
                                                 close1 Prims.int_one
                                                   close_wp
                                                  in
                                               let uu____6942 =
                                                 close1 Prims.int_zero
                                                   trivial_wp
                                                  in
                                               let uu____6944 =
                                                 let uu____6945 =
                                                   let uu____6946 =
                                                     close1 Prims.int_zero
                                                       ([], repr)
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____6946
                                                    in
                                                 let uu____6964 =
                                                   close1 Prims.int_zero
                                                     return_repr
                                                    in
                                                 let uu____6966 =
                                                   close1 Prims.int_one
                                                     bind_repr
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.monad_m
                                                     = uu____6945;
                                                   FStar_Syntax_Syntax.monad_ret
                                                     = uu____6964;
                                                   FStar_Syntax_Syntax.monad_bind
                                                     = uu____6966
                                                 }  in
                                               let uu____6968 =
                                                 FStar_Util.map_opt interp
                                                   (close1 Prims.int_zero)
                                                  in
                                               let uu____6972 =
                                                 FStar_Util.map_opt mrelation
                                                   (close1 Prims.int_zero)
                                                  in
                                               let uu____6976 =
                                                 FStar_List.map close_action
                                                   actions
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.cattributes
                                                   =
                                                   (uu___759_6928.FStar_Syntax_Syntax.cattributes);
                                                 FStar_Syntax_Syntax.mname =
                                                   (uu___759_6928.FStar_Syntax_Syntax.mname);
                                                 FStar_Syntax_Syntax.univs =
                                                   univs1;
                                                 FStar_Syntax_Syntax.binders
                                                   = effect_params;
                                                 FStar_Syntax_Syntax.spec =
                                                   uu____6929;
                                                 FStar_Syntax_Syntax.signature
                                                   = signature2;
                                                 FStar_Syntax_Syntax.if_then_else
                                                   = uu____6934;
                                                 FStar_Syntax_Syntax.ite_wp =
                                                   uu____6936;
                                                 FStar_Syntax_Syntax.stronger
                                                   = uu____6938;
                                                 FStar_Syntax_Syntax.close_wp
                                                   = uu____6940;
                                                 FStar_Syntax_Syntax.trivial
                                                   = uu____6942;
                                                 FStar_Syntax_Syntax.repr =
                                                   uu____6944;
                                                 FStar_Syntax_Syntax.elaborated
                                                   =
                                                   (uu___759_6928.FStar_Syntax_Syntax.elaborated);
                                                 FStar_Syntax_Syntax.spec_dm4f
                                                   =
                                                   (uu___759_6928.FStar_Syntax_Syntax.spec_dm4f);
                                                 FStar_Syntax_Syntax.interp =
                                                   uu____6968;
                                                 FStar_Syntax_Syntax.mrelation
                                                   = uu____6972;
                                                 FStar_Syntax_Syntax.actions
                                                   = uu____6976;
                                                 FStar_Syntax_Syntax.eff_attrs
                                                   =
                                                   (uu___759_6928.FStar_Syntax_Syntax.eff_attrs)
                                               }  in
                                             ed3)))))))))
  
let tc_lex_t :
  'Auu____6990 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____6990 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____7025 = FStar_List.hd ses  in
            uu____7025.FStar_Syntax_Syntax.sigrng  in
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
           | uu____7030 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____7036,[],t,uu____7038,uu____7039);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____7041;
               FStar_Syntax_Syntax.sigattrs = uu____7042;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____7044,_t_top,_lex_t_top,_7078,uu____7047);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____7049;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____7050;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____7052,_t_cons,_lex_t_cons,_7086,uu____7055);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____7057;
                 FStar_Syntax_Syntax.sigattrs = uu____7058;_}::[]
               when
               ((_7078 = Prims.int_zero) && (_7086 = Prims.int_zero)) &&
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
                 let uu____7111 =
                   let uu____7118 =
                     let uu____7119 =
                       let uu____7126 =
                         let uu____7129 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____7129
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____7126, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____7119  in
                   FStar_Syntax_Syntax.mk uu____7118  in
                 uu____7111 FStar_Pervasives_Native.None r1  in
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
                   let uu____7144 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7144
                    in
                 let hd1 =
                   let uu____7146 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7146
                    in
                 let tl1 =
                   let uu____7148 =
                     let uu____7149 =
                       let uu____7156 =
                         let uu____7157 =
                           let uu____7164 =
                             let uu____7167 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____7167
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____7164, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____7157  in
                       FStar_Syntax_Syntax.mk uu____7156  in
                     uu____7149 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7148
                    in
                 let res =
                   let uu____7173 =
                     let uu____7180 =
                       let uu____7181 =
                         let uu____7188 =
                           let uu____7191 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____7191
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____7188,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____7181  in
                     FStar_Syntax_Syntax.mk uu____7180  in
                   uu____7173 FStar_Pervasives_Native.None r2  in
                 let uu____7194 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____7194
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
               let uu____7233 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____7233;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____7238 ->
               let err_msg =
                 let uu____7243 =
                   let uu____7245 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____7245  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____7243
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
    fun uu____7270  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____7270 with
          | (uvs,t) ->
              let uu____7283 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____7283 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____7295 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____7295 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____7313 =
                        let uu____7316 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____7316
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____7313)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7339 =
          let uu____7340 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7340 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7339 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7365 =
          let uu____7366 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7366 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7365 r
  
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
          (let uu____7415 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____7415
           then
             let uu____7418 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____7418
           else ());
          (let uu____7423 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____7423 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____7454 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____7454 FStar_List.flatten  in
               ((let uu____7468 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____7471 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____7471)
                    in
                 if uu____7468
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
                           let uu____7487 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____7497,uu____7498,uu____7499,uu____7500,uu____7501)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____7510 -> failwith "Impossible!"  in
                           match uu____7487 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Inductive type "
                                      (Prims.op_Hat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____7529 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____7539,uu____7540,ty_lid,uu____7542,uu____7543)
                               -> (data_lid, ty_lid)
                           | uu____7550 -> failwith "Impossible"  in
                         match uu____7529 with
                         | (data_lid,ty_lid) ->
                             let uu____7558 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____7561 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____7561)
                                in
                             if uu____7558
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Exception "
                                      (Prims.op_Hat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____7575 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____7580,uu____7581,uu____7582,uu____7583,uu____7584)
                         -> lid
                     | uu____7593 -> failwith "Impossible"  in
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
                   let uu____7611 =
                     (((FStar_List.length tcs) = Prims.int_zero) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____7611
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
          let pop1 uu____7686 =
            let uu____7687 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___929_7697  ->
               match () with
               | () ->
                   let uu____7704 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____7704 (fun r  -> pop1 (); r)) ()
          with | uu___928_7735 -> (pop1 (); FStar_Exn.raise uu___928_7735)
  
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
      | uu____8051 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____8109 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____8109 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____8134 .
    'Auu____8134 FStar_Pervasives_Native.option -> 'Auu____8134 Prims.list
  =
  fun uu___0_8143  ->
    match uu___0_8143 with
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
            let uu____8223 = collect1 tl1  in
            (match uu____8223 with
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
        | ((e,n1)::uu____8461,[]) ->
            FStar_Pervasives_Native.Some (e, n1, Prims.int_zero)
        | ([],(e,n1)::uu____8517) ->
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
          let uu____8727 =
            let uu____8729 = FStar_Options.ide ()  in
            Prims.op_Negation uu____8729  in
          if uu____8727
          then
            let uu____8732 =
              let uu____8737 = FStar_TypeChecker_Env.dsenv env  in
              let uu____8738 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____8737 uu____8738  in
            (match uu____8732 with
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
                              let uu____8771 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____8772 =
                                let uu____8778 =
                                  let uu____8780 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____8782 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____8780 uu____8782
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____8778)
                                 in
                              FStar_Errors.log_issue uu____8771 uu____8772
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____8789 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____8790 =
                                   let uu____8796 =
                                     let uu____8798 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____8798
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____8796)
                                    in
                                 FStar_Errors.log_issue uu____8789 uu____8790)
                              else ())
                         else ())))
          else ()
      | uu____8808 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____8853 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____8881 ->
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
             let uu____8941 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____8941
             then
               let ses1 =
                 let uu____8949 =
                   let uu____8950 =
                     let uu____8951 =
                       tc_inductive
                         (let uu___1061_8960 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1061_8960.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1061_8960.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1061_8960.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1061_8960.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1061_8960.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1061_8960.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1061_8960.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1061_8960.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1061_8960.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1061_8960.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1061_8960.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1061_8960.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1061_8960.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1061_8960.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1061_8960.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1061_8960.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1061_8960.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1061_8960.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1061_8960.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1061_8960.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1061_8960.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___1061_8960.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1061_8960.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1061_8960.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1061_8960.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1061_8960.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1061_8960.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1061_8960.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1061_8960.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1061_8960.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1061_8960.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1061_8960.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1061_8960.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1061_8960.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1061_8960.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1061_8960.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1061_8960.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1061_8960.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1061_8960.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1061_8960.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1061_8960.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1061_8960.FStar_TypeChecker_Env.strict_args_tab)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____8951
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____8950
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____8949
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____8974 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____8974
                 then
                   let uu____8979 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1065_8983 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1065_8983.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1065_8983.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1065_8983.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1065_8983.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____8979
                 else ());
                ses1)
             else ses  in
           let uu____8993 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____8993 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___1072_9017 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1072_9017.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1072_9017.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1072_9017.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1072_9017.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let forfree =
             let uu____9031 =
               let uu____9032 =
                 FStar_Syntax_Subst.compress
                   (ne.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                  in
               uu____9032.FStar_Syntax_Syntax.n  in
             match uu____9031 with
             | FStar_Syntax_Syntax.Tm_unknown  -> false
             | uu____9037 ->
                 Prims.op_Negation ne.FStar_Syntax_Syntax.elaborated
              in
           if forfree
           then
             ((let uu____9050 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____9050
               then FStar_Util.print_string "Beginning DM4F run\n"
               else ());
              (let uu____9057 = cps_and_elaborate_ed env0 ne  in
               match uu____9057 with
               | (ses,ne1,lift_from_pure_opt) ->
                   let ne2 =
                     let uu___1090_9090 = ne1  in
                     {
                       FStar_Syntax_Syntax.cattributes =
                         (uu___1090_9090.FStar_Syntax_Syntax.cattributes);
                       FStar_Syntax_Syntax.mname =
                         (uu___1090_9090.FStar_Syntax_Syntax.mname);
                       FStar_Syntax_Syntax.univs =
                         (uu___1090_9090.FStar_Syntax_Syntax.univs);
                       FStar_Syntax_Syntax.binders =
                         (uu___1090_9090.FStar_Syntax_Syntax.binders);
                       FStar_Syntax_Syntax.spec =
                         (uu___1090_9090.FStar_Syntax_Syntax.spec);
                       FStar_Syntax_Syntax.signature =
                         (uu___1090_9090.FStar_Syntax_Syntax.signature);
                       FStar_Syntax_Syntax.if_then_else =
                         (uu___1090_9090.FStar_Syntax_Syntax.if_then_else);
                       FStar_Syntax_Syntax.ite_wp =
                         (uu___1090_9090.FStar_Syntax_Syntax.ite_wp);
                       FStar_Syntax_Syntax.stronger =
                         (uu___1090_9090.FStar_Syntax_Syntax.stronger);
                       FStar_Syntax_Syntax.close_wp =
                         (uu___1090_9090.FStar_Syntax_Syntax.close_wp);
                       FStar_Syntax_Syntax.trivial =
                         (uu___1090_9090.FStar_Syntax_Syntax.trivial);
                       FStar_Syntax_Syntax.repr =
                         (uu___1090_9090.FStar_Syntax_Syntax.repr);
                       FStar_Syntax_Syntax.elaborated = true;
                       FStar_Syntax_Syntax.spec_dm4f =
                         (uu___1090_9090.FStar_Syntax_Syntax.spec_dm4f);
                       FStar_Syntax_Syntax.interp =
                         (uu___1090_9090.FStar_Syntax_Syntax.interp);
                       FStar_Syntax_Syntax.mrelation =
                         (uu___1090_9090.FStar_Syntax_Syntax.mrelation);
                       FStar_Syntax_Syntax.actions =
                         (uu___1090_9090.FStar_Syntax_Syntax.actions);
                       FStar_Syntax_Syntax.eff_attrs =
                         (uu___1090_9090.FStar_Syntax_Syntax.eff_attrs)
                     }  in
                   let effect_and_lift_ses =
                     match lift_from_pure_opt with
                     | FStar_Pervasives_Native.Some lift ->
                         [(let uu___1095_9099 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne2);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1095_9099.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___1095_9099.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1095_9099.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1095_9099.FStar_Syntax_Syntax.sigattrs)
                           });
                         lift]
                     | FStar_Pervasives_Native.None  ->
                         [(let uu___1098_9101 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne2);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1098_9101.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___1098_9101.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1098_9101.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1098_9101.FStar_Syntax_Syntax.sigattrs)
                           })]
                      in
                   ([], (FStar_List.append ses effect_and_lift_ses), env0)))
           else
             (let ne1 =
                let uu____9109 =
                  (FStar_Options.use_two_phase_tc ()) &&
                    (FStar_TypeChecker_Env.should_verify env)
                   in
                if uu____9109
                then
                  let ne1 =
                    let uu____9113 =
                      let uu____9114 =
                        let uu____9115 =
                          tc_eff_decl
                            (let uu___1102_9117 = env  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1102_9117.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1102_9117.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1102_9117.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1102_9117.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1102_9117.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1102_9117.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1102_9117.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1102_9117.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1102_9117.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1102_9117.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___1102_9117.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1102_9117.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1102_9117.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1102_9117.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___1102_9117.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___1102_9117.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1102_9117.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___1102_9117.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1102_9117.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1102_9117.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1102_9117.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 = true;
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1102_9117.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1102_9117.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1102_9117.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1102_9117.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1102_9117.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1102_9117.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1102_9117.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1102_9117.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1102_9117.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1102_9117.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1102_9117.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1102_9117.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1102_9117.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1102_9117.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1102_9117.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___1102_9117.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1102_9117.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1102_9117.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1102_9117.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1102_9117.FStar_TypeChecker_Env.nbe);
                               FStar_TypeChecker_Env.strict_args_tab =
                                 (uu___1102_9117.FStar_TypeChecker_Env.strict_args_tab)
                             }) se ne
                           in
                        FStar_All.pipe_right uu____9115
                          (fun ne1  ->
                             let uu___1105_9123 = se  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___1105_9123.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___1105_9123.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___1105_9123.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___1105_9123.FStar_Syntax_Syntax.sigattrs)
                             })
                         in
                      FStar_All.pipe_right uu____9114
                        (FStar_TypeChecker_Normalize.elim_uvars env)
                       in
                    FStar_All.pipe_right uu____9113
                      FStar_Syntax_Util.eff_decl_of_new_effect
                     in
                  ((let uu____9125 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "TwoPhases")
                       in
                    if uu____9125
                    then
                      let uu____9130 =
                        FStar_Syntax_Print.sigelt_to_string
                          (let uu___1109_9134 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne1);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1109_9134.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___1109_9134.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1109_9134.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1109_9134.FStar_Syntax_Syntax.sigattrs)
                           })
                         in
                      FStar_Util.print1 "Effect decl after phase 1: %s\n"
                        uu____9130
                    else ());
                   ne1)
                else ne  in
              let ne2 = tc_eff_decl env se ne1  in
              let se1 =
                let uu___1114_9142 = se  in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_new_effect ne2);
                  FStar_Syntax_Syntax.sigrng =
                    (uu___1114_9142.FStar_Syntax_Syntax.sigrng);
                  FStar_Syntax_Syntax.sigquals =
                    (uu___1114_9142.FStar_Syntax_Syntax.sigquals);
                  FStar_Syntax_Syntax.sigmeta =
                    (uu___1114_9142.FStar_Syntax_Syntax.sigmeta);
                  FStar_Syntax_Syntax.sigattrs =
                    (uu___1114_9142.FStar_Syntax_Syntax.sigattrs)
                }  in
              ([se1], [], env0))
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env
               sub1.FStar_Syntax_Syntax.source
              in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env
               sub1.FStar_Syntax_Syntax.target
              in
           let uu____9150 =
             let uu____9157 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9157
              in
           (match uu____9150 with
            | (a,wp_a_src) ->
                let uu____9174 =
                  let uu____9181 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____9181
                   in
                (match uu____9174 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____9199 =
                         let uu____9202 =
                           let uu____9203 =
                             let uu____9210 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____9210)  in
                           FStar_Syntax_Syntax.NT uu____9203  in
                         [uu____9202]  in
                       FStar_Syntax_Subst.subst uu____9199 wp_b_tgt  in
                     let expected_k =
                       let uu____9218 =
                         let uu____9227 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____9234 =
                           let uu____9243 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____9243]  in
                         uu____9227 :: uu____9234  in
                       let uu____9268 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____9218 uu____9268  in
                     let repr_type eff_name a1 wp =
                       (let uu____9290 =
                          let uu____9292 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name
                             in
                          Prims.op_Negation uu____9292  in
                        if uu____9290
                        then
                          let uu____9295 =
                            let uu____9301 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____9301)
                             in
                          let uu____9305 =
                            FStar_TypeChecker_Env.get_range env  in
                          FStar_Errors.raise_error uu____9295 uu____9305
                        else ());
                       (let uu____9308 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name
                           in
                        match uu____9308 with
                        | FStar_Pervasives_Native.None  ->
                            failwith
                              "internal error: reifiable effect has no decl?"
                        | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                            let repr =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [FStar_Syntax_Syntax.U_unknown] env ed
                                ([],
                                  ((ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m))
                               in
                            let uu____9345 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____9346 =
                              let uu____9353 =
                                let uu____9354 =
                                  let uu____9371 =
                                    let uu____9382 =
                                      FStar_Syntax_Syntax.as_arg a1  in
                                    let uu____9391 =
                                      let uu____9402 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____9402]  in
                                    uu____9382 :: uu____9391  in
                                  (repr, uu____9371)  in
                                FStar_Syntax_Syntax.Tm_app uu____9354  in
                              FStar_Syntax_Syntax.mk uu____9353  in
                            uu____9346 FStar_Pervasives_Native.None
                              uu____9345)
                        in
                     let uu____9447 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____9620 =
                             if (FStar_List.length uvs) > Prims.int_zero
                             then
                               let uu____9631 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____9631 with
                               | (usubst,uvs1) ->
                                   let uu____9654 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____9655 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____9654, uu____9655)
                             else (env, lift_wp)  in
                           (match uu____9620 with
                            | (env1,lift_wp1) ->
                                let lift_wp2 =
                                  if (FStar_List.length uvs) = Prims.int_zero
                                  then check_and_gen env1 lift_wp1 expected_k
                                  else
                                    (let lift_wp2 =
                                       tc_check_trivial_guard env1 lift_wp1
                                         expected_k
                                        in
                                     let uu____9705 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____9705))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____9776 =
                             if (FStar_List.length what) > Prims.int_zero
                             then
                               let uu____9791 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____9791 with
                               | (usubst,uvs) ->
                                   let uu____9816 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____9816)
                             else ([], lift)  in
                           (match uu____9776 with
                            | (uvs,lift1) ->
                                ((let uu____9852 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____9852
                                  then
                                    let uu____9856 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____9856
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____9862 =
                                    let uu____9869 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____9869 lift1
                                     in
                                  match uu____9862 with
                                  | (lift2,comp,uu____9894) ->
                                      let uu____9895 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____9895 with
                                       | (uu____9924,lift_wp,lift_elab) ->
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
                                             let uu____9956 =
                                               let uu____9967 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____9967
                                                in
                                             let uu____9984 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____9956, uu____9984)
                                           else
                                             (let uu____10013 =
                                                let uu____10024 =
                                                  let uu____10033 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____10033)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____10024
                                                 in
                                              let uu____10048 =
                                                let uu____10057 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____10057)  in
                                              (uu____10013, uu____10048))))))
                        in
                     (match uu____9447 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___1190_10131 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1190_10131.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1190_10131.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1190_10131.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1190_10131.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1190_10131.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1190_10131.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1190_10131.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1190_10131.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1190_10131.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1190_10131.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1190_10131.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1190_10131.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1190_10131.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1190_10131.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1190_10131.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1190_10131.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1190_10131.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1190_10131.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1190_10131.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1190_10131.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1190_10131.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1190_10131.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1190_10131.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1190_10131.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1190_10131.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1190_10131.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1190_10131.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1190_10131.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1190_10131.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1190_10131.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1190_10131.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1190_10131.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1190_10131.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1190_10131.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1190_10131.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1190_10131.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1190_10131.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1190_10131.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1190_10131.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1190_10131.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1190_10131.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1190_10131.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1190_10131.FStar_TypeChecker_Env.strict_args_tab)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____10188 =
                                  let uu____10193 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____10193 with
                                  | (usubst,uvs1) ->
                                      let uu____10216 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____10217 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____10216, uu____10217)
                                   in
                                (match uu____10188 with
                                 | (env2,lift2) ->
                                     let uu____10230 =
                                       let uu____10237 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____10237
                                        in
                                     (match uu____10230 with
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
                                              let uu____10271 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____10272 =
                                                let uu____10279 =
                                                  let uu____10280 =
                                                    let uu____10297 =
                                                      let uu____10308 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____10317 =
                                                        let uu____10328 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____10328]  in
                                                      uu____10308 ::
                                                        uu____10317
                                                       in
                                                    (lift_wp1, uu____10297)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10280
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____10279
                                                 in
                                              uu____10272
                                                FStar_Pervasives_Native.None
                                                uu____10271
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____10376 =
                                              let uu____10385 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____10392 =
                                                let uu____10401 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____10408 =
                                                  let uu____10417 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____10417]  in
                                                uu____10401 :: uu____10408
                                                 in
                                              uu____10385 :: uu____10392  in
                                            let uu____10448 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____10376 uu____10448
                                             in
                                          let uu____10451 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____10451 with
                                           | (expected_k2,uu____10469,uu____10470)
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
                                                    let uu____10494 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____10494))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____10510 =
                              let uu____10512 =
                                let uu____10514 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____10514
                                  FStar_List.length
                                 in
                              uu____10512 <> Prims.int_one  in
                            if uu____10510
                            then
                              let uu____10537 =
                                let uu____10543 =
                                  let uu____10545 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____10547 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10549 =
                                    let uu____10551 =
                                      let uu____10553 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10553
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10551
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____10545 uu____10547 uu____10549
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____10543)
                                 in
                              FStar_Errors.raise_error uu____10537 r
                            else ());
                           (let uu____10580 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____10591 =
                                   let uu____10593 =
                                     let uu____10596 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____10596
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____10593
                                     FStar_List.length
                                    in
                                 uu____10591 <> Prims.int_one)
                               in
                            if uu____10580
                            then
                              let uu____10650 =
                                let uu____10656 =
                                  let uu____10658 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____10660 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10662 =
                                    let uu____10664 =
                                      let uu____10666 =
                                        let uu____10669 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____10669
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10666
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10664
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____10658 uu____10660 uu____10662
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____10656)
                                 in
                              FStar_Errors.raise_error uu____10650 r
                            else ());
                           (let sub2 =
                              let uu___1227_10728 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___1227_10728.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___1227_10728.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___1230_10730 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___1230_10730.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___1230_10730.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___1230_10730.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___1230_10730.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let uu____10744 =
             if (FStar_List.length uvs) = Prims.int_zero
             then (env, uvs, tps, c)
             else
               (let uu____10772 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____10772 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____10803 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____10803 c  in
                    let uu____10812 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____10812, uvs1, tps1, c1))
              in
           (match uu____10744 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____10834 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____10834 with
                 | (tps2,c2) ->
                     let uu____10851 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____10851 with
                      | (tps3,env3,us) ->
                          let uu____10871 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____10871 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____10899)::uu____10900 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____10919 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____10927 =
                                   let uu____10929 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____10929  in
                                 if uu____10927
                                 then
                                   let uu____10932 =
                                     let uu____10938 =
                                       let uu____10940 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____10942 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____10940 uu____10942
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____10938)
                                      in
                                   FStar_Errors.raise_error uu____10932 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____10950 =
                                   let uu____10951 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____10951
                                    in
                                 match uu____10950 with
                                 | (uvs2,t) ->
                                     let uu____10982 =
                                       let uu____10987 =
                                         let uu____11000 =
                                           let uu____11001 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____11001.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____11000)  in
                                       match uu____10987 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____11016,c5)) -> ([], c5)
                                       | (uu____11058,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____11097 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____10982 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               Prims.int_one
                                           then
                                             (let uu____11131 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____11131 with
                                              | (uu____11136,t1) ->
                                                  let uu____11138 =
                                                    let uu____11144 =
                                                      let uu____11146 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____11148 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____11152 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____11146
                                                        uu____11148
                                                        uu____11152
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____11144)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____11138 r)
                                           else ();
                                           (let se1 =
                                              let uu___1300_11159 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___1300_11159.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___1300_11159.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___1300_11159.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___1300_11159.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____11166,uu____11167,uu____11168) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_11173  ->
                   match uu___1_11173 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____11176 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____11182,uu____11183) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_11192  ->
                   match uu___1_11192 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____11195 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____11206 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____11206
             then
               let uu____11209 =
                 let uu____11215 =
                   let uu____11217 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____11217
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____11215)
                  in
               FStar_Errors.raise_error uu____11209 r
             else ());
            (let uu____11223 =
               let uu____11232 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____11232
               then
                 let uu____11243 =
                   tc_declare_typ
                     (let uu___1324_11246 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1324_11246.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1324_11246.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1324_11246.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1324_11246.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1324_11246.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1324_11246.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1324_11246.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1324_11246.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1324_11246.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1324_11246.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1324_11246.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1324_11246.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1324_11246.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1324_11246.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1324_11246.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1324_11246.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1324_11246.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1324_11246.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1324_11246.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1324_11246.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1324_11246.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1324_11246.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1324_11246.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1324_11246.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1324_11246.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1324_11246.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1324_11246.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1324_11246.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1324_11246.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1324_11246.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1324_11246.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1324_11246.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1324_11246.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1324_11246.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1324_11246.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1324_11246.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1324_11246.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1324_11246.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1324_11246.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1324_11246.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___1324_11246.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___1324_11246.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1324_11246.FStar_TypeChecker_Env.strict_args_tab)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____11243 with
                 | (uvs1,t1) ->
                     ((let uu____11271 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____11271
                       then
                         let uu____11276 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____11278 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____11276 uu____11278
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____11223 with
             | (uvs1,t1) ->
                 let uu____11313 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____11313 with
                  | (uvs2,t2) ->
                      ([(let uu___1337_11343 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1337_11343.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1337_11343.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1337_11343.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1337_11343.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____11348 =
             let uu____11357 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____11357
             then
               let uu____11368 =
                 tc_assume
                   (let uu___1346_11371 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1346_11371.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1346_11371.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1346_11371.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1346_11371.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1346_11371.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1346_11371.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1346_11371.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1346_11371.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1346_11371.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1346_11371.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1346_11371.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1346_11371.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1346_11371.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1346_11371.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1346_11371.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1346_11371.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1346_11371.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1346_11371.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1346_11371.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1346_11371.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1346_11371.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___1346_11371.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1346_11371.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1346_11371.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1346_11371.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1346_11371.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1346_11371.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1346_11371.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1346_11371.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1346_11371.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1346_11371.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1346_11371.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1346_11371.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1346_11371.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1346_11371.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1346_11371.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1346_11371.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1346_11371.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1346_11371.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1346_11371.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1346_11371.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1346_11371.FStar_TypeChecker_Env.strict_args_tab)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____11368 with
               | (uvs1,t1) ->
                   ((let uu____11397 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____11397
                     then
                       let uu____11402 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____11404 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____11402
                         uu____11404
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____11348 with
            | (uvs1,t1) ->
                let uu____11439 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____11439 with
                 | (uvs2,t2) ->
                     ([(let uu___1359_11469 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1359_11469.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1359_11469.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1359_11469.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1359_11469.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____11473 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____11473 with
            | (e1,c,g1) ->
                let uu____11493 =
                  let uu____11500 =
                    let uu____11503 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____11503  in
                  let uu____11504 =
                    let uu____11509 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____11509)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____11500 uu____11504
                   in
                (match uu____11493 with
                 | (e2,uu____11521,g) ->
                     ((let uu____11524 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____11524);
                      (let se1 =
                         let uu___1374_11526 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1374_11526.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1374_11526.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1374_11526.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1374_11526.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____11538 = FStar_Options.debug_any ()  in
             if uu____11538
             then
               let uu____11541 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____11543 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____11541
                 uu____11543
             else ());
            (let uu____11548 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____11548 with
             | (t1,uu____11566,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____11580 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____11580 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____11583 =
                              let uu____11589 =
                                let uu____11591 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____11593 =
                                  let uu____11595 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____11595
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____11591 uu____11593
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____11589)
                               in
                            FStar_Errors.raise_error uu____11583 r
                        | uu____11607 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___1395_11612 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1395_11612.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1395_11612.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1395_11612.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1395_11612.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1395_11612.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1395_11612.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1395_11612.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1395_11612.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1395_11612.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1395_11612.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1395_11612.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1395_11612.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1395_11612.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1395_11612.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1395_11612.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1395_11612.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1395_11612.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1395_11612.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1395_11612.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1395_11612.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___1395_11612.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1395_11612.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1395_11612.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1395_11612.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1395_11612.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1395_11612.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1395_11612.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1395_11612.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1395_11612.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1395_11612.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1395_11612.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1395_11612.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1395_11612.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1395_11612.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1395_11612.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1395_11612.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1395_11612.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1395_11612.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1395_11612.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1395_11612.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1395_11612.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___1395_11612.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1395_11612.FStar_TypeChecker_Env.strict_args_tab)
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
                 let uu____11680 =
                   let uu____11682 =
                     let uu____11691 = drop_logic val_q  in
                     let uu____11694 = drop_logic q'  in
                     (uu____11691, uu____11694)  in
                   match uu____11682 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____11680
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____11721 =
                      let uu____11727 =
                        let uu____11729 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____11731 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____11733 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____11729 uu____11731 uu____11733
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____11727)
                       in
                    FStar_Errors.raise_error uu____11721 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____11770 =
                   let uu____11771 = FStar_Syntax_Subst.compress def  in
                   uu____11771.FStar_Syntax_Syntax.n  in
                 match uu____11770 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____11783,uu____11784) -> binders
                 | uu____11809 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____11821;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____11926) -> val_bs1
                     | (uu____11957,[]) -> val_bs1
                     | ((body_bv,uu____11989)::bt,(val_bv,aqual)::vt) ->
                         let uu____12046 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____12070) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___1464_12084 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___1466_12087 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___1466_12087.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___1464_12084.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1464_12084.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____12046
                      in
                   let uu____12094 =
                     let uu____12101 =
                       let uu____12102 =
                         let uu____12117 = rename_binders1 def_bs val_bs  in
                         (uu____12117, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____12102  in
                     FStar_Syntax_Syntax.mk uu____12101  in
                   uu____12094 FStar_Pervasives_Native.None r1
               | uu____12136 -> typ1  in
             let uu___1472_12137 = lb  in
             let uu____12138 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___1472_12137.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1472_12137.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____12138;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1472_12137.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___1472_12137.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1472_12137.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1472_12137.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____12141 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____12196  ->
                     fun lb  ->
                       match uu____12196 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____12242 =
                             let uu____12254 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____12254 with
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
                                   | uu____12334 ->
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
                                  (let uu____12381 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____12381, quals_opt1)))
                              in
                           (match uu____12242 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____12141 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____12485 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___2_12491  ->
                                match uu___2_12491 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____12496 -> false))
                         in
                      if uu____12485
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____12509 =
                    let uu____12516 =
                      let uu____12517 =
                        let uu____12531 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____12531)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____12517  in
                    FStar_Syntax_Syntax.mk uu____12516  in
                  uu____12509 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___1515_12550 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1515_12550.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1515_12550.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1515_12550.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1515_12550.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1515_12550.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1515_12550.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1515_12550.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1515_12550.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1515_12550.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1515_12550.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1515_12550.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1515_12550.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1515_12550.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1515_12550.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1515_12550.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1515_12550.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1515_12550.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1515_12550.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1515_12550.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1515_12550.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1515_12550.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1515_12550.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1515_12550.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1515_12550.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1515_12550.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1515_12550.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1515_12550.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1515_12550.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1515_12550.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1515_12550.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1515_12550.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1515_12550.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1515_12550.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1515_12550.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1515_12550.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1515_12550.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1515_12550.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1515_12550.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1515_12550.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1515_12550.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1515_12550.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___1515_12550.FStar_TypeChecker_Env.strict_args_tab)
                  }  in
                let e1 =
                  let uu____12553 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____12553
                  then
                    let drop_lbtyp e_lax =
                      let uu____12562 =
                        let uu____12563 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____12563.FStar_Syntax_Syntax.n  in
                      match uu____12562 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____12585 =
                              let uu____12586 = FStar_Syntax_Subst.compress e
                                 in
                              uu____12586.FStar_Syntax_Syntax.n  in
                            match uu____12585 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____12590,lb1::[]),uu____12592) ->
                                let uu____12608 =
                                  let uu____12609 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____12609.FStar_Syntax_Syntax.n  in
                                (match uu____12608 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____12614 -> false)
                            | uu____12616 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___1540_12620 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___1542_12635 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___1542_12635.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___1542_12635.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___1542_12635.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___1542_12635.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___1542_12635.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___1542_12635.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___1540_12620.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___1540_12620.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____12638 -> e_lax  in
                    let uu____12639 =
                      FStar_Util.record_time
                        (fun uu____12647  ->
                           let uu____12648 =
                             let uu____12649 =
                               let uu____12650 =
                                 FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                   (let uu___1546_12659 = env'  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___1546_12659.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___1546_12659.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___1546_12659.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___1546_12659.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___1546_12659.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___1546_12659.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___1546_12659.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___1546_12659.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___1546_12659.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___1546_12659.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___1546_12659.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___1546_12659.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___1546_12659.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___1546_12659.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___1546_12659.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___1546_12659.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___1546_12659.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___1546_12659.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___1546_12659.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___1546_12659.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___1546_12659.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___1546_12659.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___1546_12659.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___1546_12659.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___1546_12659.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___1546_12659.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___1546_12659.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___1546_12659.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___1546_12659.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___1546_12659.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___1546_12659.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___1546_12659.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___1546_12659.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___1546_12659.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___1546_12659.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___1546_12659.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___1546_12659.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___1546_12659.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___1546_12659.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___1546_12659.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___1546_12659.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___1546_12659.FStar_TypeChecker_Env.strict_args_tab)
                                    }) e
                                  in
                               FStar_All.pipe_right uu____12650
                                 (fun uu____12672  ->
                                    match uu____12672 with
                                    | (e1,uu____12680,uu____12681) -> e1)
                                in
                             FStar_All.pipe_right uu____12649
                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                  env')
                              in
                           FStar_All.pipe_right uu____12648 drop_lbtyp)
                       in
                    match uu____12639 with
                    | (e1,ms) ->
                        ((let uu____12687 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TwoPhases")
                             in
                          if uu____12687
                          then
                            let uu____12692 =
                              FStar_Syntax_Print.term_to_string e1  in
                            FStar_Util.print1
                              "Let binding after phase 1: %s\n" uu____12692
                          else ());
                         (let uu____12698 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TCDeclTime")
                             in
                          if uu____12698
                          then
                            let uu____12703 = FStar_Util.string_of_int ms  in
                            FStar_Util.print1
                              "Let binding elaborated (phase 1) in %s milliseconds\n"
                              uu____12703
                          else ());
                         e1)
                  else e  in
                let uu____12710 =
                  let uu____12719 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____12719 with
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
                (match uu____12710 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___1576_12824 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___1576_12824.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1576_12824.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1576_12824.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1576_12824.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___1583_12837 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1583_12837.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1583_12837.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___1583_12837.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___1583_12837.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1583_12837.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1583_12837.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____12838 =
                       FStar_Util.record_time
                         (fun uu____12857  ->
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              env' e1)
                        in
                     (match uu____12838 with
                      | (r1,ms) ->
                          ((let uu____12885 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TCDeclTime")
                               in
                            if uu____12885
                            then
                              let uu____12890 = FStar_Util.string_of_int ms
                                 in
                              FStar_Util.print1
                                "Let binding typechecked in phase 2 in %s milliseconds\n"
                                uu____12890
                            else ());
                           (let uu____12895 =
                              match r1 with
                              | ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                                   FStar_Syntax_Syntax.pos = uu____12920;
                                   FStar_Syntax_Syntax.vars = uu____12921;_},uu____12922,g)
                                  when FStar_TypeChecker_Env.is_trivial g ->
                                  let lbs2 =
                                    let uu____12952 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.snd lbs1)
                                        (FStar_List.map rename_parameters)
                                       in
                                    ((FStar_Pervasives_Native.fst lbs1),
                                      uu____12952)
                                     in
                                  let lbs3 =
                                    let uu____12976 =
                                      match post_tau with
                                      | FStar_Pervasives_Native.Some tau ->
                                          FStar_List.map (postprocess_lb tau)
                                            (FStar_Pervasives_Native.snd lbs2)
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.snd lbs2
                                       in
                                    ((FStar_Pervasives_Native.fst lbs2),
                                      uu____12976)
                                     in
                                  let quals1 =
                                    match e2.FStar_Syntax_Syntax.n with
                                    | FStar_Syntax_Syntax.Tm_meta
                                        (uu____12999,FStar_Syntax_Syntax.Meta_desugared
                                         (FStar_Syntax_Syntax.Masked_effect
                                         ))
                                        ->
                                        FStar_Syntax_Syntax.HasMaskedEffect
                                        :: quals
                                    | uu____13004 -> quals  in
                                  ((let uu___1613_13013 = se1  in
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_let
                                           (lbs3, lids));
                                      FStar_Syntax_Syntax.sigrng =
                                        (uu___1613_13013.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals = quals1;
                                      FStar_Syntax_Syntax.sigmeta =
                                        (uu___1613_13013.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (uu___1613_13013.FStar_Syntax_Syntax.sigattrs)
                                    }), lbs3)
                              | uu____13016 ->
                                  failwith
                                    "impossible (typechecking should preserve Tm_let)"
                               in
                            match uu____12895 with
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
                                 (let uu____13072 = log env1  in
                                  if uu____13072
                                  then
                                    let uu____13075 =
                                      let uu____13077 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.snd lbs1)
                                          (FStar_List.map
                                             (fun lb  ->
                                                let should_log =
                                                  let uu____13097 =
                                                    let uu____13106 =
                                                      let uu____13107 =
                                                        let uu____13110 =
                                                          FStar_Util.right
                                                            lb.FStar_Syntax_Syntax.lbname
                                                           in
                                                        uu____13110.FStar_Syntax_Syntax.fv_name
                                                         in
                                                      uu____13107.FStar_Syntax_Syntax.v
                                                       in
                                                    FStar_TypeChecker_Env.try_lookup_val_decl
                                                      env1 uu____13106
                                                     in
                                                  match uu____13097 with
                                                  | FStar_Pervasives_Native.None
                                                       -> true
                                                  | uu____13119 -> false  in
                                                if should_log
                                                then
                                                  let uu____13131 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  let uu____13133 =
                                                    FStar_Syntax_Print.term_to_string
                                                      lb.FStar_Syntax_Syntax.lbtyp
                                                     in
                                                  FStar_Util.format2
                                                    "let %s : %s" uu____13131
                                                    uu____13133
                                                else ""))
                                         in
                                      FStar_All.pipe_right uu____13077
                                        (FStar_String.concat "\n")
                                       in
                                    FStar_Util.print1 "%s\n" uu____13075
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
      (let uu____13185 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____13185
       then
         let uu____13188 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____13188
       else ());
      (let uu____13193 = get_fail_se se  in
       match uu____13193 with
       | FStar_Pervasives_Native.Some (uu____13214,false ) when
           let uu____13231 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____13231 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___1644_13257 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___1644_13257.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___1644_13257.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___1644_13257.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___1644_13257.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___1644_13257.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___1644_13257.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___1644_13257.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___1644_13257.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___1644_13257.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___1644_13257.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___1644_13257.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___1644_13257.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___1644_13257.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___1644_13257.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___1644_13257.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___1644_13257.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___1644_13257.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___1644_13257.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___1644_13257.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___1644_13257.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___1644_13257.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___1644_13257.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___1644_13257.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___1644_13257.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___1644_13257.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___1644_13257.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___1644_13257.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___1644_13257.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___1644_13257.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___1644_13257.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___1644_13257.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___1644_13257.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___1644_13257.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___1644_13257.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___1644_13257.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___1644_13257.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___1644_13257.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___1644_13257.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___1644_13257.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___1644_13257.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___1644_13257.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___1644_13257.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___1644_13257.FStar_TypeChecker_Env.strict_args_tab)
               }
             else env1  in
           ((let uu____13262 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____13262
             then
               let uu____13265 =
                 let uu____13267 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____13267
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____13265
             else ());
            (let uu____13281 =
               FStar_Errors.catch_errors
                 (fun uu____13311  ->
                    FStar_Options.with_saved_options
                      (fun uu____13323  -> tc_decl' env' se))
                in
             match uu____13281 with
             | (errs,uu____13335) ->
                 ((let uu____13365 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____13365
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____13400 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____13400  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____13412 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____13423 =
                            let uu____13433 = check_multi_eq errnos1 actual
                               in
                            match uu____13433 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- Prims.int_one), (~- Prims.int_one),
                                  (~- Prims.int_one))
                             in
                          (match uu____13423 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____13498 =
                                   let uu____13504 =
                                     let uu____13506 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____13509 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____13512 =
                                       FStar_Util.string_of_int e  in
                                     let uu____13514 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____13516 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____13506 uu____13509 uu____13512
                                       uu____13514 uu____13516
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____13504)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____13498)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____13543 .
    'Auu____13543 ->
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
               (fun uu___3_13586  ->
                  match uu___3_13586 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____13589 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____13600) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____13608 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____13618 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____13623 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____13639 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____13665 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13691) ->
            let uu____13700 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13700
            then
              let for_export_bundle se1 uu____13737 =
                match uu____13737 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____13776,uu____13777) ->
                         let dec =
                           let uu___1720_13787 = se1  in
                           let uu____13788 =
                             let uu____13789 =
                               let uu____13796 =
                                 let uu____13797 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____13797  in
                               (l, us, uu____13796)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____13789
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____13788;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1720_13787.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1720_13787.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1720_13787.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____13807,uu____13808,uu____13809) ->
                         let dec =
                           let uu___1731_13817 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1731_13817.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1731_13817.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1731_13817.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____13822 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____13845,uu____13846,uu____13847) ->
            let uu____13848 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13848 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____13872 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____13872
            then
              ([(let uu___1747_13891 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___1747_13891.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___1747_13891.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___1747_13891.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____13894 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_13900  ->
                         match uu___4_13900 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____13903 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____13909 ->
                             true
                         | uu____13911 -> false))
                  in
               if uu____13894 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____13932 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____13937 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____13942 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13947 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13965) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____13979 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____13979
            then ([], hidden)
            else
              (let dec =
                 let uu____14000 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____14000;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____14011 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____14011
            then
              let uu____14022 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1782_14036 = se  in
                        let uu____14037 =
                          let uu____14038 =
                            let uu____14045 =
                              let uu____14046 =
                                let uu____14049 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____14049.FStar_Syntax_Syntax.fv_name  in
                              uu____14046.FStar_Syntax_Syntax.v  in
                            (uu____14045, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____14038  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____14037;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1782_14036.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1782_14036.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1782_14036.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____14022, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____14072 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____14072
       then
         let uu____14075 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____14075
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____14080 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____14098 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
           uu____14115) ->
           let env1 =
             let uu___1803_14120 = env  in
             let uu____14121 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1803_14120.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1803_14120.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1803_14120.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1803_14120.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1803_14120.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1803_14120.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1803_14120.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1803_14120.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1803_14120.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1803_14120.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1803_14120.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1803_14120.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1803_14120.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1803_14120.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1803_14120.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1803_14120.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1803_14120.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1803_14120.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1803_14120.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1803_14120.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1803_14120.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1803_14120.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1803_14120.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1803_14120.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1803_14120.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1803_14120.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1803_14120.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1803_14120.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1803_14120.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1803_14120.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1803_14120.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1803_14120.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1803_14120.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1803_14120.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14121;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1803_14120.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1803_14120.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1803_14120.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1803_14120.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1803_14120.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1803_14120.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1803_14120.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1803_14120.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1803_14120.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
           let env1 =
             let uu___1803_14123 = env  in
             let uu____14124 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1803_14123.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1803_14123.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1803_14123.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1803_14123.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1803_14123.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1803_14123.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1803_14123.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1803_14123.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1803_14123.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1803_14123.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1803_14123.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1803_14123.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1803_14123.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1803_14123.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1803_14123.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1803_14123.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1803_14123.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1803_14123.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1803_14123.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1803_14123.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1803_14123.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1803_14123.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1803_14123.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1803_14123.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1803_14123.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1803_14123.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1803_14123.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1803_14123.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1803_14123.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1803_14123.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1803_14123.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1803_14123.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1803_14123.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1803_14123.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14124;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1803_14123.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1803_14123.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1803_14123.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1803_14123.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1803_14123.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1803_14123.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1803_14123.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1803_14123.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1803_14123.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions
           uu____14125) ->
           let env1 =
             let uu___1803_14128 = env  in
             let uu____14129 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1803_14128.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1803_14128.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1803_14128.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1803_14128.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1803_14128.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1803_14128.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1803_14128.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1803_14128.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1803_14128.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1803_14128.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1803_14128.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1803_14128.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1803_14128.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1803_14128.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1803_14128.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1803_14128.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1803_14128.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1803_14128.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1803_14128.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1803_14128.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1803_14128.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1803_14128.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1803_14128.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1803_14128.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1803_14128.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1803_14128.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1803_14128.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1803_14128.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1803_14128.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1803_14128.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1803_14128.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1803_14128.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1803_14128.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1803_14128.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14129;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1803_14128.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1803_14128.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1803_14128.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1803_14128.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1803_14128.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1803_14128.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1803_14128.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1803_14128.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1803_14128.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____14130) ->
           let env1 =
             let uu___1803_14135 = env  in
             let uu____14136 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1803_14135.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1803_14135.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1803_14135.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1803_14135.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1803_14135.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1803_14135.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1803_14135.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1803_14135.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1803_14135.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1803_14135.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1803_14135.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1803_14135.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1803_14135.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1803_14135.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1803_14135.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1803_14135.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1803_14135.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1803_14135.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1803_14135.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1803_14135.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1803_14135.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1803_14135.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1803_14135.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1803_14135.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1803_14135.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1803_14135.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1803_14135.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1803_14135.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1803_14135.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1803_14135.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1803_14135.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1803_14135.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1803_14135.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1803_14135.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____14136;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1803_14135.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1803_14135.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1803_14135.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1803_14135.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1803_14135.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1803_14135.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1803_14135.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1803_14135.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1803_14135.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver )
           ->
           ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
              ();
            env)
       | FStar_Syntax_Syntax.Sig_pragma uu____14138 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____14148 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____14148) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____14149,uu____14150,uu____14151) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_14156  ->
                   match uu___5_14156 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____14159 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____14161,uu____14162) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_14171  ->
                   match uu___5_14171 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____14174 -> false))
           -> env
       | uu____14176 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____14245 se =
        match uu____14245 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____14298 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____14298
              then
                let uu____14301 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____14301
              else ());
             (let uu____14306 = tc_decl env1 se  in
              match uu____14306 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____14359 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____14359
                             then
                               let uu____14363 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____14363
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____14379 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____14379
                             then
                               let uu____14383 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____14383
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
                    (let uu____14400 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____14400
                     then
                       let uu____14405 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____14414 =
                                  let uu____14416 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____14416 "\n"  in
                                Prims.op_Hat s uu____14414) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____14405
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____14426 =
                       let uu____14435 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____14435
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____14477 se1 =
                            match uu____14477 with
                            | (exports1,hidden1) ->
                                let uu____14505 = for_export env3 hidden1 se1
                                   in
                                (match uu____14505 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____14426 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____14659 = acc  in
        match uu____14659 with
        | (uu____14694,uu____14695,env1,uu____14697) ->
            let uu____14710 =
              FStar_Util.record_time
                (fun uu____14757  -> process_one_decl acc se)
               in
            (match uu____14710 with
             | (r,ms_elapsed) ->
                 ((let uu____14823 =
                     ((FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TCDeclTime"))
                        ||
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.attr_eq
                              FStar_Syntax_Util.tcdecltime_attr)
                           se.FStar_Syntax_Syntax.sigattrs))
                       || (FStar_Options.timing ())
                      in
                   if uu____14823
                   then
                     let uu____14827 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____14829 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____14827 uu____14829
                   else ());
                  r))
         in
      let uu____14834 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____14834 with
      | (ses1,exports,env1,uu____14882) ->
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
          let uu___1898_14920 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1898_14920.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1898_14920.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1898_14920.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1898_14920.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1898_14920.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1898_14920.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1898_14920.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1898_14920.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1898_14920.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1898_14920.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___1898_14920.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1898_14920.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1898_14920.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1898_14920.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1898_14920.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___1898_14920.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1898_14920.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___1898_14920.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1898_14920.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___1898_14920.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1898_14920.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1898_14920.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1898_14920.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1898_14920.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1898_14920.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1898_14920.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1898_14920.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1898_14920.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1898_14920.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1898_14920.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1898_14920.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1898_14920.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1898_14920.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1898_14920.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___1898_14920.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___1898_14920.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1898_14920.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1898_14920.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1898_14920.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1898_14920.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1898_14920.FStar_TypeChecker_Env.strict_args_tab)
          }  in
        let check_term lid univs1 t =
          let uu____14940 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____14940 with
          | (univs2,t1) ->
              ((let uu____14948 =
                  let uu____14950 =
                    let uu____14956 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____14956  in
                  FStar_All.pipe_left uu____14950
                    (FStar_Options.Other "Exports")
                   in
                if uu____14948
                then
                  let uu____14960 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____14962 =
                    let uu____14964 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____14964
                      (FStar_String.concat ", ")
                     in
                  let uu____14981 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____14960 uu____14962 uu____14981
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____14987 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____14987 (fun a1  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____15013 =
             let uu____15015 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____15017 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____15015 uu____15017
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____15013);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15028) ->
              let uu____15037 =
                let uu____15039 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15039  in
              if uu____15037
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____15053,uu____15054) ->
              let t =
                let uu____15066 =
                  let uu____15073 =
                    let uu____15074 =
                      let uu____15089 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____15089)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____15074  in
                  FStar_Syntax_Syntax.mk uu____15073  in
                uu____15066 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____15105,uu____15106,uu____15107) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____15117 =
                let uu____15119 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15119  in
              if uu____15117 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____15127,lbs),uu____15129) ->
              let uu____15140 =
                let uu____15142 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15142  in
              if uu____15140
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
              let uu____15165 =
                let uu____15167 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15167  in
              if uu____15165
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____15188 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____15189 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____15196 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____15197 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____15198 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____15205 -> ()  in
        let uu____15206 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____15206 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____15312) -> true
             | uu____15314 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____15344 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____15383 ->
                   let uu____15384 =
                     let uu____15391 =
                       let uu____15392 =
                         let uu____15407 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____15407)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____15392  in
                     FStar_Syntax_Syntax.mk uu____15391  in
                   uu____15384 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____15424,uu____15425) ->
            let s1 =
              let uu___2022_15435 = s  in
              let uu____15436 =
                let uu____15437 =
                  let uu____15444 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____15444)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____15437  in
              let uu____15445 =
                let uu____15448 =
                  let uu____15451 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____15451  in
                FStar_Syntax_Syntax.Assumption :: uu____15448  in
              {
                FStar_Syntax_Syntax.sigel = uu____15436;
                FStar_Syntax_Syntax.sigrng =
                  (uu___2022_15435.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____15445;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2022_15435.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___2022_15435.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____15454 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____15479 lbdef =
        match uu____15479 with
        | (uvs,t) ->
            let attrs =
              let uu____15490 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____15490
              then
                let uu____15495 =
                  let uu____15496 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____15496
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____15495 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___2035_15499 = s  in
            let uu____15500 =
              let uu____15503 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____15503  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___2035_15499.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____15500;
              FStar_Syntax_Syntax.sigmeta =
                (uu___2035_15499.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____15521 -> failwith "Impossible!"  in
        let c_opt =
          let uu____15528 = FStar_Syntax_Util.is_unit t  in
          if uu____15528
          then
            let uu____15535 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____15535
          else
            (let uu____15542 =
               let uu____15543 = FStar_Syntax_Subst.compress t  in
               uu____15543.FStar_Syntax_Syntax.n  in
             match uu____15542 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____15550,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____15574 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____15586 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____15586
            then false
            else
              (let uu____15593 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____15593
               then true
               else
                 (let uu____15600 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____15600))
         in
      let extract_sigelt s =
        (let uu____15612 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____15612
         then
           let uu____15615 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____15615
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____15622 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____15642 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____15661 ->
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
                             (lid,uu____15707,uu____15708,uu____15709,uu____15710,uu____15711)
                             ->
                             ((let uu____15721 =
                                 let uu____15724 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____15724  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____15721);
                              (let uu____15773 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____15773 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____15777,uu____15778,uu____15779,uu____15780,uu____15781)
                             ->
                             ((let uu____15789 =
                                 let uu____15792 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____15792  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____15789);
                              sigelts1)
                         | uu____15841 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____15850 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15850
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____15860 =
                    let uu___2099_15861 = s  in
                    let uu____15862 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2099_15861.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2099_15861.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15862;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2099_15861.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2099_15861.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15860])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____15873 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15873
             then []
             else
               (let uu____15880 = lbs  in
                match uu____15880 with
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
                        (fun uu____15942  ->
                           match uu____15942 with
                           | (uu____15950,t,uu____15952) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____15969  ->
                             match uu____15969 with
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
                           (fun uu____15996  ->
                              match uu____15996 with
                              | (uu____16004,t,uu____16006) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____16018,uu____16019) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____16027 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____16056 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____16056) uu____16027
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____16060 =
                    let uu___2141_16061 = s  in
                    let uu____16062 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2141_16061.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2141_16061.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____16062;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2141_16061.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2141_16061.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____16060]
                else [])
             else
               (let uu____16069 =
                  let uu___2143_16070 = s  in
                  let uu____16071 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___2143_16070.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___2143_16070.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____16071;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___2143_16070.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___2143_16070.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____16069])
         | FStar_Syntax_Syntax.Sig_new_effect uu____16074 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____16075 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____16076 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____16089 -> [s])
         in
      let uu___2153_16090 = m  in
      let uu____16091 =
        let uu____16092 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____16092 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___2153_16090.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____16091;
        FStar_Syntax_Syntax.exports =
          (uu___2153_16090.FStar_Syntax_Syntax.exports);
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
        (fun uu____16143  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____16190  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____16205 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____16205
  
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
      (let uu____16294 = FStar_Options.debug_any ()  in
       if uu____16294
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
         let uu___2178_16310 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___2178_16310.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___2178_16310.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___2178_16310.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___2178_16310.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___2178_16310.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___2178_16310.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___2178_16310.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___2178_16310.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___2178_16310.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___2178_16310.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___2178_16310.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___2178_16310.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___2178_16310.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___2178_16310.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___2178_16310.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___2178_16310.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___2178_16310.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___2178_16310.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___2178_16310.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___2178_16310.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___2178_16310.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___2178_16310.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___2178_16310.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___2178_16310.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___2178_16310.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___2178_16310.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___2178_16310.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___2178_16310.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___2178_16310.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___2178_16310.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___2178_16310.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___2178_16310.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___2178_16310.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___2178_16310.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___2178_16310.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___2178_16310.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___2178_16310.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___2178_16310.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___2178_16310.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___2178_16310.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___2178_16310.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___2178_16310.FStar_TypeChecker_Env.strict_args_tab)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____16312 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____16312 with
       | (ses,exports,env3) ->
           ((let uu___2186_16345 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___2186_16345.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___2186_16345.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___2186_16345.FStar_Syntax_Syntax.is_interface)
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
        let uu____16374 = tc_decls env decls  in
        match uu____16374 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___2195_16405 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___2195_16405.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___2195_16405.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___2195_16405.FStar_Syntax_Syntax.is_interface)
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
        let uu____16466 = tc_partial_modul env01 m  in
        match uu____16466 with
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
                (let uu____16503 = FStar_Errors.get_err_count ()  in
                 uu____16503 = Prims.int_zero)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____16514 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____16514
                then
                  let uu____16518 =
                    let uu____16520 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16520 then "" else " (in lax mode) "  in
                  let uu____16528 =
                    let uu____16530 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16530
                    then
                      let uu____16534 =
                        let uu____16536 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.op_Hat uu____16536 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____16534
                    else ""  in
                  let uu____16543 =
                    let uu____16545 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16545
                    then
                      let uu____16549 =
                        let uu____16551 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____16551 "\n"  in
                      Prims.op_Hat "\nto: " uu____16549
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____16518
                    uu____16528 uu____16543
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___2221_16565 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2221_16565.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2221_16565.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2221_16565.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2221_16565.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2221_16565.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2221_16565.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2221_16565.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2221_16565.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2221_16565.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2221_16565.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2221_16565.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2221_16565.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2221_16565.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2221_16565.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2221_16565.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2221_16565.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2221_16565.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2221_16565.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2221_16565.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2221_16565.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2221_16565.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2221_16565.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2221_16565.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2221_16565.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2221_16565.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2221_16565.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2221_16565.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2221_16565.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2221_16565.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2221_16565.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2221_16565.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___2221_16565.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2221_16565.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2221_16565.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2221_16565.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2221_16565.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2221_16565.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2221_16565.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2221_16565.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2221_16565.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2221_16565.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2221_16565.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2221_16565.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let en02 =
                    let uu___2224_16567 = en01  in
                    let uu____16568 =
                      let uu____16583 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____16583, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2224_16567.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2224_16567.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2224_16567.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2224_16567.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2224_16567.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2224_16567.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2224_16567.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2224_16567.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2224_16567.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2224_16567.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2224_16567.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2224_16567.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2224_16567.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2224_16567.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2224_16567.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2224_16567.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2224_16567.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2224_16567.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2224_16567.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2224_16567.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2224_16567.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2224_16567.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2224_16567.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2224_16567.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2224_16567.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2224_16567.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2224_16567.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2224_16567.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2224_16567.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2224_16567.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2224_16567.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____16568;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2224_16567.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2224_16567.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2224_16567.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2224_16567.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2224_16567.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2224_16567.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2224_16567.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2224_16567.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2224_16567.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___2224_16567.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2224_16567.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2224_16567.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let uu____16629 =
                    let uu____16631 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____16631  in
                  if uu____16629
                  then
                    ((let uu____16635 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____16635 (fun a2  -> ()));
                     en02)
                  else en02  in
                let uu____16639 = tc_modul en0 modul_iface true  in
                match uu____16639 with
                | (modul_iface1,env) ->
                    ((let uu___2233_16652 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___2233_16652.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___2233_16652.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___2233_16652.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___2235_16656 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___2235_16656.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___2235_16656.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___2235_16656.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____16659 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____16659 FStar_Util.smap_clear);
               (let uu____16695 =
                  ((let uu____16699 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____16699) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____16702 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____16702)
                   in
                if uu____16695 then check_exports env modul exports else ());
               (let uu____16708 =
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____16708 (fun a3  -> ()));
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
        let uu____16723 =
          let uu____16725 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____16725  in
        push_context env uu____16723  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____16746 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____16757 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____16757 with | (uu____16764,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____16789 = FStar_Options.debug_any ()  in
         if uu____16789
         then
           let uu____16792 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____16792
         else ());
        (let uu____16804 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____16804
         then
           let uu____16807 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____16807
         else ());
        (let env1 =
           let uu___2265_16813 = env  in
           let uu____16814 =
             let uu____16816 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____16816  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___2265_16813.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___2265_16813.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___2265_16813.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___2265_16813.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___2265_16813.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___2265_16813.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___2265_16813.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___2265_16813.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___2265_16813.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___2265_16813.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___2265_16813.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___2265_16813.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___2265_16813.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___2265_16813.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___2265_16813.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___2265_16813.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___2265_16813.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___2265_16813.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___2265_16813.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___2265_16813.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____16814;
             FStar_TypeChecker_Env.lax_universes =
               (uu___2265_16813.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___2265_16813.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___2265_16813.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___2265_16813.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___2265_16813.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___2265_16813.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___2265_16813.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___2265_16813.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___2265_16813.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___2265_16813.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___2265_16813.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___2265_16813.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___2265_16813.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___2265_16813.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___2265_16813.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___2265_16813.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___2265_16813.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___2265_16813.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___2265_16813.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___2265_16813.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___2265_16813.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___2265_16813.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___2265_16813.FStar_TypeChecker_Env.strict_args_tab)
           }  in
         let uu____16818 = tc_modul env1 m b  in
         match uu____16818 with
         | (m1,env2) ->
             ((let uu____16830 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____16830
               then
                 let uu____16833 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____16833
               else ());
              (let uu____16839 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____16839
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
                         let uu____16877 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____16877 with
                         | (univnames1,e) ->
                             let uu___2287_16884 = lb  in
                             let uu____16885 =
                               let uu____16888 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____16888 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2287_16884.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2287_16884.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___2287_16884.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2287_16884.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16885;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2287_16884.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2287_16884.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___2289_16889 = se  in
                       let uu____16890 =
                         let uu____16891 =
                           let uu____16898 =
                             let uu____16899 = FStar_List.map update lbs  in
                             (b1, uu____16899)  in
                           (uu____16898, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____16891  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____16890;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___2289_16889.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___2289_16889.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___2289_16889.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___2289_16889.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____16907 -> se  in
                 let normalized_module =
                   let uu___2293_16909 = m1  in
                   let uu____16910 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___2293_16909.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____16910;
                     FStar_Syntax_Syntax.exports =
                       (uu___2293_16909.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___2293_16909.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____16911 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____16911
               else ());
              (m1, env2)))
  