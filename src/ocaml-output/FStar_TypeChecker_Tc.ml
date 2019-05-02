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
        else (Prims.parse_int "0")  in
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
              (uu___16_73.FStar_TypeChecker_Env.nbe)
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
              (uu___25_137.FStar_TypeChecker_Env.nbe)
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
                                        FStar_Syntax_Syntax.assert_p =
                                          (uu___153_945.FStar_Syntax_Syntax.assert_p);
                                        FStar_Syntax_Syntax.assume_p =
                                          (uu___153_945.FStar_Syntax_Syntax.assume_p);
                                        FStar_Syntax_Syntax.null_wp =
                                          (uu___153_945.FStar_Syntax_Syntax.null_wp);
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
                                                    = (Prims.parse_int "0")
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
                                                                  FStar_Syntax_Syntax.assert_p
                                                                    =
                                                                    (
                                                                    uu___336_2991.FStar_Syntax_Syntax.assert_p);
                                                                  FStar_Syntax_Syntax.assume_p
                                                                    =
                                                                    (
                                                                    uu___336_2991.FStar_Syntax_Syntax.assume_p);
                                                                  FStar_Syntax_Syntax.null_wp
                                                                    =
                                                                    (
                                                                    uu___336_2991.FStar_Syntax_Syntax.null_wp);
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
                                                                    (Prims.parse_int "0")
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
                 open_univs_binders (Prims.parse_int "0")
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
                                FStar_Syntax_Syntax.assert_p =
                                  (uu___375_3246.FStar_Syntax_Syntax.assert_p);
                                FStar_Syntax_Syntax.assume_p =
                                  (uu___375_3246.FStar_Syntax_Syntax.assume_p);
                                FStar_Syntax_Syntax.null_wp =
                                  (uu___375_3246.FStar_Syntax_Syntax.null_wp);
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
                                    op ed1.FStar_Syntax_Syntax.assert_p  in
                                  let uu____3354 =
                                    op ed1.FStar_Syntax_Syntax.assume_p  in
                                  let uu____3355 =
                                    op ed1.FStar_Syntax_Syntax.null_wp  in
                                  let uu____3356 =
                                    op ed1.FStar_Syntax_Syntax.trivial  in
                                  let uu____3357 =
                                    let uu____3358 =
                                      let uu____3359 =
                                        op
                                          ([],
                                            ((ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m))
                                         in
                                      FStar_Pervasives_Native.snd uu____3359
                                       in
                                    let uu____3370 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                       in
                                    let uu____3371 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                       in
                                    {
                                      FStar_Syntax_Syntax.monad_m =
                                        uu____3358;
                                      FStar_Syntax_Syntax.monad_ret =
                                        uu____3370;
                                      FStar_Syntax_Syntax.monad_bind =
                                        uu____3371
                                    }  in
                                  let uu____3372 =
                                    FStar_List.map
                                      (fun a  ->
                                         let uu___390_3380 = a  in
                                         let uu____3381 =
                                           let uu____3382 =
                                             op
                                               ((a.FStar_Syntax_Syntax.action_univs),
                                                 (a.FStar_Syntax_Syntax.action_defn))
                                              in
                                           FStar_Pervasives_Native.snd
                                             uu____3382
                                            in
                                         let uu____3393 =
                                           let uu____3394 =
                                             op
                                               ((a.FStar_Syntax_Syntax.action_univs),
                                                 (a.FStar_Syntax_Syntax.action_typ))
                                              in
                                           FStar_Pervasives_Native.snd
                                             uu____3394
                                            in
                                         {
                                           FStar_Syntax_Syntax.action_name =
                                             (uu___390_3380.FStar_Syntax_Syntax.action_name);
                                           FStar_Syntax_Syntax.action_unqualified_name
                                             =
                                             (uu___390_3380.FStar_Syntax_Syntax.action_unqualified_name);
                                           FStar_Syntax_Syntax.action_univs =
                                             (uu___390_3380.FStar_Syntax_Syntax.action_univs);
                                           FStar_Syntax_Syntax.action_params
                                             =
                                             (uu___390_3380.FStar_Syntax_Syntax.action_params);
                                           FStar_Syntax_Syntax.action_defn =
                                             uu____3381;
                                           FStar_Syntax_Syntax.action_typ =
                                             uu____3393
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
                                    FStar_Syntax_Syntax.assert_p = uu____3353;
                                    FStar_Syntax_Syntax.assume_p = uu____3354;
                                    FStar_Syntax_Syntax.null_wp = uu____3355;
                                    FStar_Syntax_Syntax.trivial = uu____3356;
                                    FStar_Syntax_Syntax.repr = uu____3357;
                                    FStar_Syntax_Syntax.elaborated =
                                      (uu___387_3333.FStar_Syntax_Syntax.elaborated);
                                    FStar_Syntax_Syntax.spec_dm4f =
                                      (uu___387_3333.FStar_Syntax_Syntax.spec_dm4f);
                                    FStar_Syntax_Syntax.interp =
                                      (uu___387_3333.FStar_Syntax_Syntax.interp);
                                    FStar_Syntax_Syntax.mrelation =
                                      (uu___387_3333.FStar_Syntax_Syntax.mrelation);
                                    FStar_Syntax_Syntax.actions = uu____3372;
                                    FStar_Syntax_Syntax.eff_attrs =
                                      (uu___387_3333.FStar_Syntax_Syntax.eff_attrs)
                                  }
                               in
                            ((let uu____3406 =
                                FStar_TypeChecker_Env.debug env0
                                  (FStar_Options.Other "ED")
                                 in
                              if uu____3406
                              then
                                let uu____3410 =
                                  FStar_Syntax_Print.eff_decl_to_string ed2
                                   in
                                FStar_Util.print1
                                  "eff_decl after opening:\n\t%s\n"
                                  uu____3410
                              else ());
                             (let wp_with_fresh_result_type env2 mname
                                signature2 =
                                let fail1 t =
                                  let uu____3449 =
                                    FStar_TypeChecker_Err.unexpected_signature_for_monad
                                      env2 mname t
                                     in
                                  let uu____3455 =
                                    FStar_Ident.range_of_lid mname  in
                                  FStar_Errors.raise_error uu____3449
                                    uu____3455
                                   in
                                let uu____3462 =
                                  let uu____3463 =
                                    FStar_Syntax_Subst.compress signature2
                                     in
                                  uu____3463.FStar_Syntax_Syntax.n  in
                                match uu____3462 with
                                | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                    let bs1 =
                                      FStar_Syntax_Subst.open_binders bs  in
                                    (match bs1 with
                                     | (a,uu____3502)::(wp,uu____3504)::[] ->
                                         (a, (wp.FStar_Syntax_Syntax.sort))
                                     | uu____3533 -> fail1 signature2)
                                | uu____3534 -> fail1 signature2  in
                              let uu____3535 =
                                wp_with_fresh_result_type env1
                                  ed2.FStar_Syntax_Syntax.mname signature1
                                 in
                              match uu____3535 with
                              | (a,wp_a) ->
                                  let fresh_effect_signature uu____3559 =
                                    match annotated_univ_names with
                                    | [] ->
                                        let uu____3566 =
                                          FStar_TypeChecker_TcTerm.tc_trivial_guard
                                            env1 signature_un
                                           in
                                        (match uu____3566 with
                                         | (signature2,uu____3578) ->
                                             wp_with_fresh_result_type env1
                                               ed2.FStar_Syntax_Syntax.mname
                                               signature2)
                                    | uu____3579 ->
                                        let uu____3582 =
                                          let uu____3587 =
                                            let uu____3588 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                annotated_univ_names
                                                signature1
                                               in
                                            (annotated_univ_names,
                                              uu____3588)
                                             in
                                          FStar_TypeChecker_Env.inst_tscheme
                                            uu____3587
                                           in
                                        (match uu____3582 with
                                         | (uu____3601,signature2) ->
                                             wp_with_fresh_result_type env1
                                               ed2.FStar_Syntax_Syntax.mname
                                               signature2)
                                     in
                                  let env2 =
                                    let uu____3604 =
                                      FStar_Syntax_Syntax.new_bv
                                        FStar_Pervasives_Native.None
                                        signature1
                                       in
                                    FStar_TypeChecker_Env.push_bv env1
                                      uu____3604
                                     in
                                  ((let uu____3606 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env0)
                                        (FStar_Options.Other "ED")
                                       in
                                    if uu____3606
                                    then
                                      let uu____3611 =
                                        FStar_Syntax_Print.lid_to_string
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      let uu____3613 =
                                        FStar_Syntax_Print.binders_to_string
                                          " " ed2.FStar_Syntax_Syntax.binders
                                         in
                                      let uu____3616 =
                                        FStar_Syntax_Print.term_to_string
                                          signature1
                                         in
                                      let uu____3618 =
                                        let uu____3620 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Print.term_to_string
                                          uu____3620
                                         in
                                      let uu____3621 =
                                        FStar_Syntax_Print.term_to_string
                                          a.FStar_Syntax_Syntax.sort
                                         in
                                      FStar_Util.print5
                                        "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                        uu____3611 uu____3613 uu____3616
                                        uu____3618 uu____3621
                                    else ());
                                   (let check_and_gen' env3 uu____3656 k =
                                      match uu____3656 with
                                      | (us,t) ->
                                          (match annotated_univ_names with
                                           | [] -> check_and_gen env3 t k
                                           | uu____3692::uu____3693 ->
                                               let uu____3696 =
                                                 FStar_Syntax_Subst.subst_tscheme
                                                   open_annotated_univs
                                                   (us, t)
                                                  in
                                               (match uu____3696 with
                                                | (us1,t1) ->
                                                    let uu____3719 =
                                                      FStar_Syntax_Subst.open_univ_vars
                                                        us1 t1
                                                       in
                                                    (match uu____3719 with
                                                     | (us2,t2) ->
                                                         let uu____3734 =
                                                           let uu____3735 =
                                                             FStar_TypeChecker_Env.push_univ_vars
                                                               env3 us2
                                                              in
                                                           tc_check_trivial_guard
                                                             uu____3735 t2 k
                                                            in
                                                         let uu____3736 =
                                                           FStar_Syntax_Subst.close_univ_vars
                                                             us2 t2
                                                            in
                                                         (us2, uu____3736))))
                                       in
                                    let return_wp =
                                      let expected_k =
                                        let uu____3755 =
                                          let uu____3764 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____3771 =
                                            let uu____3780 =
                                              let uu____3787 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____3787
                                               in
                                            [uu____3780]  in
                                          uu____3764 :: uu____3771  in
                                        let uu____3806 =
                                          FStar_Syntax_Syntax.mk_GTotal wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____3755
                                          uu____3806
                                         in
                                      check_and_gen' env2
                                        (ed2.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                        expected_k
                                       in
                                    let bind_wp =
                                      let uu____3810 =
                                        fresh_effect_signature ()  in
                                      match uu____3810 with
                                      | (b,wp_b) ->
                                          let a_wp_b =
                                            let uu____3826 =
                                              let uu____3835 =
                                                let uu____3842 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____3842
                                                 in
                                              [uu____3835]  in
                                            let uu____3855 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_b
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____3826 uu____3855
                                             in
                                          let expected_k =
                                            let uu____3861 =
                                              let uu____3870 =
                                                FStar_Syntax_Syntax.null_binder
                                                  FStar_Syntax_Syntax.t_range
                                                 in
                                              let uu____3877 =
                                                let uu____3886 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____3893 =
                                                  let uu____3902 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____3909 =
                                                    let uu____3918 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_a
                                                       in
                                                    let uu____3925 =
                                                      let uu____3934 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          a_wp_b
                                                         in
                                                      [uu____3934]  in
                                                    uu____3918 :: uu____3925
                                                     in
                                                  uu____3902 :: uu____3909
                                                   in
                                                uu____3886 :: uu____3893  in
                                              uu____3870 :: uu____3877  in
                                            let uu____3977 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_b
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____3861 uu____3977
                                             in
                                          check_and_gen' env2
                                            (ed2.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                            expected_k
                                       in
                                    let mk_simple_repr t =
                                      let uu____3988 =
                                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                          env2
                                          (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                         in
                                      match uu____3988 with
                                      | (repr,uu____3998,uu____3999) ->
                                          let uu____4000 =
                                            let uu____4011 =
                                              FStar_Syntax_Syntax.as_arg t
                                               in
                                            [uu____4011]  in
                                          FStar_Syntax_Util.mk_app repr
                                            uu____4000
                                       in
                                    let interp =
                                      match ed2.FStar_Syntax_Syntax.interp
                                      with
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some interp
                                          ->
                                          let repr_a =
                                            let uu____4045 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            mk_simple_repr uu____4045  in
                                          let expected_k =
                                            let uu____4049 =
                                              let uu____4058 =
                                                FStar_Syntax_Syntax.mk_implicit_binder
                                                  a
                                                 in
                                              let uu____4065 =
                                                let uu____4074 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    repr_a
                                                   in
                                                [uu____4074]  in
                                              uu____4058 :: uu____4065  in
                                            let uu____4099 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4049 uu____4099
                                             in
                                          let uu____4102 =
                                            check_and_gen' env2 interp
                                              expected_k
                                             in
                                          FStar_All.pipe_left
                                            (fun _4105  ->
                                               FStar_Pervasives_Native.Some
                                                 _4105) uu____4102
                                       in
                                    let mrelation =
                                      match ed2.FStar_Syntax_Syntax.mrelation
                                      with
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some
                                          mrelation ->
                                          let uu____4112 =
                                            FStar_Syntax_Util.type_u ()  in
                                          (match uu____4112 with
                                           | (t,uu____4120) ->
                                               let repr_a =
                                                 let uu____4124 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     a
                                                    in
                                                 mk_simple_repr uu____4124
                                                  in
                                               let expected_k =
                                                 let uu____4128 =
                                                   let uu____4137 =
                                                     FStar_Syntax_Syntax.mk_implicit_binder
                                                       a
                                                      in
                                                   let uu____4144 =
                                                     let uu____4153 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         repr_a
                                                        in
                                                     let uu____4160 =
                                                       let uu____4169 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_a
                                                          in
                                                       [uu____4169]  in
                                                     uu____4153 :: uu____4160
                                                      in
                                                   uu____4137 :: uu____4144
                                                    in
                                                 let uu____4200 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____4128 uu____4200
                                                  in
                                               let uu____4203 =
                                                 check_and_gen' env2
                                                   mrelation expected_k
                                                  in
                                               FStar_All.pipe_left
                                                 (fun _4206  ->
                                                    FStar_Pervasives_Native.Some
                                                      _4206) uu____4203)
                                       in
                                    let if_then_else1 =
                                      let p =
                                        let uu____4217 =
                                          let uu____4220 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4220
                                           in
                                        let uu____4221 =
                                          let uu____4222 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4222
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4217
                                          uu____4221
                                         in
                                      let expected_k =
                                        let uu____4234 =
                                          let uu____4243 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4250 =
                                            let uu____4259 =
                                              FStar_Syntax_Syntax.mk_binder p
                                               in
                                            let uu____4266 =
                                              let uu____4275 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              let uu____4282 =
                                                let uu____4291 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____4291]  in
                                              uu____4275 :: uu____4282  in
                                            uu____4259 :: uu____4266  in
                                          uu____4243 :: uu____4250  in
                                        let uu____4328 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4234
                                          uu____4328
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.if_then_else
                                        expected_k
                                       in
                                    let ite_wp =
                                      let expected_k =
                                        let uu____4343 =
                                          let uu____4352 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4359 =
                                            let uu____4368 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____4368]  in
                                          uu____4352 :: uu____4359  in
                                        let uu____4393 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4343
                                          uu____4393
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.ite_wp
                                        expected_k
                                       in
                                    let stronger =
                                      let uu____4397 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____4397 with
                                      | (t,uu____4403) ->
                                          let expected_k =
                                            let uu____4407 =
                                              let uu____4416 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4423 =
                                                let uu____4432 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____4439 =
                                                  let uu____4448 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____4448]  in
                                                uu____4432 :: uu____4439  in
                                              uu____4416 :: uu____4423  in
                                            let uu____4479 =
                                              FStar_Syntax_Syntax.mk_Total t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4407 uu____4479
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.stronger
                                            expected_k
                                       in
                                    let close_wp =
                                      let b =
                                        let uu____4492 =
                                          let uu____4495 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4495
                                           in
                                        let uu____4496 =
                                          let uu____4497 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4497
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4492
                                          uu____4496
                                         in
                                      let b_wp_a =
                                        let uu____4509 =
                                          let uu____4518 =
                                            let uu____4525 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                b
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____4525
                                             in
                                          [uu____4518]  in
                                        let uu____4538 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4509
                                          uu____4538
                                         in
                                      let expected_k =
                                        let uu____4544 =
                                          let uu____4553 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4560 =
                                            let uu____4569 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____4576 =
                                              let uu____4585 =
                                                FStar_Syntax_Syntax.null_binder
                                                  b_wp_a
                                                 in
                                              [uu____4585]  in
                                            uu____4569 :: uu____4576  in
                                          uu____4553 :: uu____4560  in
                                        let uu____4616 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4544
                                          uu____4616
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.close_wp
                                        expected_k
                                       in
                                    let assert_p =
                                      let expected_k =
                                        let uu____4631 =
                                          let uu____4640 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4647 =
                                            let uu____4656 =
                                              let uu____4663 =
                                                let uu____4664 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____4664
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____4663
                                               in
                                            let uu____4673 =
                                              let uu____4682 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____4682]  in
                                            uu____4656 :: uu____4673  in
                                          uu____4640 :: uu____4647  in
                                        let uu____4713 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4631
                                          uu____4713
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.assert_p
                                        expected_k
                                       in
                                    let assume_p =
                                      let expected_k =
                                        let uu____4728 =
                                          let uu____4737 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4744 =
                                            let uu____4753 =
                                              let uu____4760 =
                                                let uu____4761 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____4761
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____4760
                                               in
                                            let uu____4770 =
                                              let uu____4779 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____4779]  in
                                            uu____4753 :: uu____4770  in
                                          uu____4737 :: uu____4744  in
                                        let uu____4810 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4728
                                          uu____4810
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.assume_p
                                        expected_k
                                       in
                                    let null_wp =
                                      let expected_k =
                                        let uu____4825 =
                                          let uu____4834 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          [uu____4834]  in
                                        let uu____4853 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4825
                                          uu____4853
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.null_wp
                                        expected_k
                                       in
                                    let trivial_wp =
                                      let uu____4857 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____4857 with
                                      | (t,uu____4863) ->
                                          let expected_k =
                                            let uu____4867 =
                                              let uu____4876 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4883 =
                                                let uu____4892 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____4892]  in
                                              uu____4876 :: uu____4883  in
                                            let uu____4917 =
                                              FStar_Syntax_Syntax.mk_GTotal t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4867 uu____4917
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.trivial
                                            expected_k
                                       in
                                    let uu____4920 =
                                      if ed2.FStar_Syntax_Syntax.spec_dm4f
                                      then
                                        let repr =
                                          let uu____4946 =
                                            FStar_Syntax_Util.type_u ()  in
                                          match uu____4946 with
                                          | (t,uu____4952) ->
                                              let expected_k =
                                                let uu____4956 =
                                                  let uu____4965 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____4972 =
                                                    let uu____4981 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_a
                                                       in
                                                    [uu____4981]  in
                                                  uu____4965 :: uu____4972
                                                   in
                                                let uu____5006 =
                                                  FStar_Syntax_Syntax.mk_GTotal
                                                    t
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____4956 uu____5006
                                                 in
                                              ((let uu____5010 =
                                                  FStar_TypeChecker_Env.debug
                                                    env2
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____5010
                                                then
                                                  let uu____5014 =
                                                    FStar_Syntax_Print.term_to_string
                                                      (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                                     in
                                                  let uu____5016 =
                                                    FStar_Syntax_Print.term_to_string
                                                      expected_k
                                                     in
                                                  FStar_Util.print2
                                                    "About to check repr=%s\nat type %s\n"
                                                    uu____5014 uu____5016
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
                                          let uu____5035 =
                                            let uu____5042 =
                                              let uu____5043 =
                                                let uu____5060 =
                                                  let uu____5071 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      t
                                                     in
                                                  let uu____5080 =
                                                    let uu____5091 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        wp
                                                       in
                                                    [uu____5091]  in
                                                  uu____5071 :: uu____5080
                                                   in
                                                (repr1, uu____5060)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____5043
                                               in
                                            FStar_Syntax_Syntax.mk uu____5042
                                             in
                                          uu____5035
                                            FStar_Pervasives_Native.None
                                            FStar_Range.dummyRange
                                           in
                                        let mk_repr a1 wp =
                                          let uu____5149 =
                                            FStar_Syntax_Syntax.bv_to_name a1
                                             in
                                          mk_repr' uu____5149 wp  in
                                        let destruct_repr t =
                                          let uu____5164 =
                                            let uu____5165 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____5165.FStar_Syntax_Syntax.n
                                             in
                                          match uu____5164 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____5176,(t1,uu____5178)::
                                               (wp,uu____5180)::[])
                                              -> (t1, wp)
                                          | uu____5239 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let bind_repr =
                                          let r =
                                            let uu____5251 =
                                              FStar_Syntax_Syntax.lid_as_fv
                                                FStar_Parser_Const.range_0
                                                FStar_Syntax_Syntax.delta_constant
                                                FStar_Pervasives_Native.None
                                               in
                                            FStar_All.pipe_right uu____5251
                                              FStar_Syntax_Syntax.fv_to_tm
                                             in
                                          let uu____5252 =
                                            fresh_effect_signature ()  in
                                          match uu____5252 with
                                          | (b,wp_b) ->
                                              let a_wp_b =
                                                let uu____5268 =
                                                  let uu____5277 =
                                                    let uu____5284 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        a
                                                       in
                                                    FStar_Syntax_Syntax.null_binder
                                                      uu____5284
                                                     in
                                                  [uu____5277]  in
                                                let uu____5297 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    wp_b
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____5268 uu____5297
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
                                                let uu____5305 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____5305
                                                 in
                                              let wp_g_x =
                                                let uu____5310 =
                                                  let uu____5315 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      wp_g
                                                     in
                                                  let uu____5316 =
                                                    let uu____5317 =
                                                      let uu____5326 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x_a
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.as_arg
                                                        uu____5326
                                                       in
                                                    [uu____5317]  in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____5315 uu____5316
                                                   in
                                                uu____5310
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____5357 =
                                                    let uu____5362 =
                                                      let uu____5363 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          bind_wp
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____5363
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    let uu____5372 =
                                                      let uu____5373 =
                                                        let uu____5376 =
                                                          let uu____5379 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          let uu____5380 =
                                                            let uu____5383 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                b
                                                               in
                                                            let uu____5384 =
                                                              let uu____5387
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_f
                                                                 in
                                                              let uu____5388
                                                                =
                                                                let uu____5391
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g
                                                                   in
                                                                [uu____5391]
                                                                 in
                                                              uu____5387 ::
                                                                uu____5388
                                                               in
                                                            uu____5383 ::
                                                              uu____5384
                                                             in
                                                          uu____5379 ::
                                                            uu____5380
                                                           in
                                                        r :: uu____5376  in
                                                      FStar_List.map
                                                        FStar_Syntax_Syntax.as_arg
                                                        uu____5373
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____5362 uu____5372
                                                     in
                                                  uu____5357
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr b wp  in
                                              let maybe_range_arg =
                                                let uu____5409 =
                                                  FStar_Util.for_some
                                                    (FStar_Syntax_Util.attr_eq
                                                       FStar_Syntax_Util.dm4f_bind_range_attr)
                                                    ed2.FStar_Syntax_Syntax.eff_attrs
                                                   in
                                                if uu____5409
                                                then
                                                  let uu____5420 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      FStar_Syntax_Syntax.t_range
                                                     in
                                                  let uu____5427 =
                                                    let uu____5436 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        FStar_Syntax_Syntax.t_range
                                                       in
                                                    [uu____5436]  in
                                                  uu____5420 :: uu____5427
                                                else []  in
                                              let expected_k =
                                                let uu____5472 =
                                                  let uu____5481 =
                                                    let uu____5490 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        a
                                                       in
                                                    let uu____5497 =
                                                      let uu____5506 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          b
                                                         in
                                                      [uu____5506]  in
                                                    uu____5490 :: uu____5497
                                                     in
                                                  let uu____5531 =
                                                    let uu____5540 =
                                                      let uu____5549 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          wp_f
                                                         in
                                                      let uu____5556 =
                                                        let uu____5565 =
                                                          let uu____5572 =
                                                            let uu____5573 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            mk_repr a
                                                              uu____5573
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____5572
                                                           in
                                                        let uu____5574 =
                                                          let uu____5583 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              wp_g
                                                             in
                                                          let uu____5590 =
                                                            let uu____5599 =
                                                              let uu____5606
                                                                =
                                                                let uu____5607
                                                                  =
                                                                  let uu____5616
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                  [uu____5616]
                                                                   in
                                                                let uu____5635
                                                                  =
                                                                  let uu____5638
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____5638
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  uu____5607
                                                                  uu____5635
                                                                 in
                                                              FStar_Syntax_Syntax.null_binder
                                                                uu____5606
                                                               in
                                                            [uu____5599]  in
                                                          uu____5583 ::
                                                            uu____5590
                                                           in
                                                        uu____5565 ::
                                                          uu____5574
                                                         in
                                                      uu____5549 ::
                                                        uu____5556
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____5540
                                                     in
                                                  FStar_List.append
                                                    uu____5481 uu____5531
                                                   in
                                                let uu____5683 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____5472 uu____5683
                                                 in
                                              ((let uu____5687 =
                                                  FStar_TypeChecker_Env.debug
                                                    env2
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____5687
                                                then
                                                  let uu____5691 =
                                                    FStar_Syntax_Print.term_to_string
                                                      expected_k
                                                     in
                                                  FStar_Util.print1
                                                    "About to check expected_k %s\n"
                                                    uu____5691
                                                else ());
                                               (let uu____5696 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env2 expected_k
                                                   in
                                                match uu____5696 with
                                                | (expected_k1,uu____5704,uu____5705)
                                                    ->
                                                    ((let uu____5707 =
                                                        FStar_TypeChecker_Env.debug
                                                          env2
                                                          (FStar_Options.Other
                                                             "ED")
                                                         in
                                                      if uu____5707
                                                      then
                                                        let uu____5711 =
                                                          FStar_Syntax_Print.term_to_string
                                                            (FStar_Pervasives_Native.snd
                                                               (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind)
                                                           in
                                                        let uu____5717 =
                                                          FStar_Syntax_Print.term_to_string
                                                            expected_k1
                                                           in
                                                        FStar_Util.print2
                                                          "About to check bind=%s\n\n, at type %s\n"
                                                          uu____5711
                                                          uu____5717
                                                      else ());
                                                     (let env3 =
                                                        FStar_TypeChecker_Env.set_range
                                                          env2
                                                          (FStar_Pervasives_Native.snd
                                                             (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind).FStar_Syntax_Syntax.pos
                                                         in
                                                      let env4 =
                                                        let uu___553_5728 =
                                                          env3  in
                                                        {
                                                          FStar_TypeChecker_Env.solver
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.solver);
                                                          FStar_TypeChecker_Env.range
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.range);
                                                          FStar_TypeChecker_Env.curmodule
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.curmodule);
                                                          FStar_TypeChecker_Env.gamma
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.gamma);
                                                          FStar_TypeChecker_Env.gamma_sig
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.gamma_sig);
                                                          FStar_TypeChecker_Env.gamma_cache
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.gamma_cache);
                                                          FStar_TypeChecker_Env.modules
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.modules);
                                                          FStar_TypeChecker_Env.expected_typ
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.expected_typ);
                                                          FStar_TypeChecker_Env.sigtab
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.sigtab);
                                                          FStar_TypeChecker_Env.attrtab
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.attrtab);
                                                          FStar_TypeChecker_Env.is_pattern
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.is_pattern);
                                                          FStar_TypeChecker_Env.instantiate_imp
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.instantiate_imp);
                                                          FStar_TypeChecker_Env.effects
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.effects);
                                                          FStar_TypeChecker_Env.generalize
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.generalize);
                                                          FStar_TypeChecker_Env.letrecs
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.letrecs);
                                                          FStar_TypeChecker_Env.top_level
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.top_level);
                                                          FStar_TypeChecker_Env.check_uvars
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.check_uvars);
                                                          FStar_TypeChecker_Env.use_eq
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.use_eq);
                                                          FStar_TypeChecker_Env.is_iface
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.is_iface);
                                                          FStar_TypeChecker_Env.admit
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.admit);
                                                          FStar_TypeChecker_Env.lax
                                                            = true;
                                                          FStar_TypeChecker_Env.lax_universes
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.lax_universes);
                                                          FStar_TypeChecker_Env.phase1
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.phase1);
                                                          FStar_TypeChecker_Env.failhard
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.failhard);
                                                          FStar_TypeChecker_Env.nosynth
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.nosynth);
                                                          FStar_TypeChecker_Env.uvar_subtyping
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.uvar_subtyping);
                                                          FStar_TypeChecker_Env.tc_term
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.tc_term);
                                                          FStar_TypeChecker_Env.type_of
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.type_of);
                                                          FStar_TypeChecker_Env.universe_of
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.universe_of);
                                                          FStar_TypeChecker_Env.check_type_of
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.check_type_of);
                                                          FStar_TypeChecker_Env.use_bv_sorts
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.use_bv_sorts);
                                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                          FStar_TypeChecker_Env.normalized_eff_names
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.normalized_eff_names);
                                                          FStar_TypeChecker_Env.fv_delta_depths
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.fv_delta_depths);
                                                          FStar_TypeChecker_Env.proof_ns
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.proof_ns);
                                                          FStar_TypeChecker_Env.synth_hook
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.synth_hook);
                                                          FStar_TypeChecker_Env.splice
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.splice);
                                                          FStar_TypeChecker_Env.postprocess
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.postprocess);
                                                          FStar_TypeChecker_Env.is_native_tactic
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.is_native_tactic);
                                                          FStar_TypeChecker_Env.identifier_info
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.identifier_info);
                                                          FStar_TypeChecker_Env.tc_hooks
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.tc_hooks);
                                                          FStar_TypeChecker_Env.dsenv
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.dsenv);
                                                          FStar_TypeChecker_Env.nbe
                                                            =
                                                            (uu___553_5728.FStar_TypeChecker_Env.nbe)
                                                        }  in
                                                      let br =
                                                        check_and_gen' env4
                                                          (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                                          expected_k1
                                                         in
                                                      (let uu____5740 =
                                                         FStar_TypeChecker_Env.debug
                                                           env4
                                                           (FStar_Options.Other
                                                              "ED")
                                                          in
                                                       if uu____5740
                                                       then
                                                         let uu____5744 =
                                                           FStar_Syntax_Print.tscheme_to_string
                                                             br
                                                            in
                                                         let uu____5746 =
                                                           FStar_Syntax_Print.term_to_string
                                                             expected_k1
                                                            in
                                                         FStar_Util.print2
                                                           "After checking bind_repr is %s\nexpected_k is %s\n"
                                                           uu____5744
                                                           uu____5746
                                                       else ());
                                                      br))))
                                           in
                                        let return_repr =
                                          let x_a =
                                            let uu____5753 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.gen_bv "x_a"
                                              FStar_Pervasives_Native.None
                                              uu____5753
                                             in
                                          let res =
                                            let wp =
                                              let uu____5761 =
                                                let uu____5766 =
                                                  let uu____5767 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      return_wp
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____5767
                                                    FStar_Pervasives_Native.snd
                                                   in
                                                let uu____5776 =
                                                  let uu____5777 =
                                                    let uu____5780 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        a
                                                       in
                                                    let uu____5781 =
                                                      let uu____5784 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x_a
                                                         in
                                                      [uu____5784]  in
                                                    uu____5780 :: uu____5781
                                                     in
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.as_arg
                                                    uu____5777
                                                   in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____5766 uu____5776
                                                 in
                                              uu____5761
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            mk_repr a wp  in
                                          let expected_k =
                                            let uu____5796 =
                                              let uu____5805 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____5812 =
                                                let uu____5821 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    x_a
                                                   in
                                                [uu____5821]  in
                                              uu____5805 :: uu____5812  in
                                            let uu____5846 =
                                              FStar_Syntax_Syntax.mk_Total
                                                res
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____5796 uu____5846
                                             in
                                          let uu____5849 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k
                                             in
                                          match uu____5849 with
                                          | (expected_k1,uu____5857,uu____5858)
                                              ->
                                              let env3 =
                                                FStar_TypeChecker_Env.set_range
                                                  env2
                                                  (FStar_Pervasives_Native.snd
                                                     (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret).FStar_Syntax_Syntax.pos
                                                 in
                                              let uu____5864 =
                                                check_and_gen' env3
                                                  (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                                  expected_k1
                                                 in
                                              (match uu____5864 with
                                               | (univs1,repr1) ->
                                                   (match univs1 with
                                                    | [] -> ([], repr1)
                                                    | uu____5887 ->
                                                        FStar_Errors.raise_error
                                                          (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                            "Unexpected universe-polymorphic return for effect")
                                                          repr1.FStar_Syntax_Syntax.pos))
                                           in
                                        let actions =
                                          let check_action act =
                                            let uu____5902 =
                                              if
                                                act.FStar_Syntax_Syntax.action_univs
                                                  = []
                                              then (env2, act)
                                              else
                                                (let uu____5916 =
                                                   FStar_Syntax_Subst.univ_var_opening
                                                     act.FStar_Syntax_Syntax.action_univs
                                                    in
                                                 match uu____5916 with
                                                 | (usubst,uvs) ->
                                                     let uu____5939 =
                                                       FStar_TypeChecker_Env.push_univ_vars
                                                         env2 uvs
                                                        in
                                                     let uu____5940 =
                                                       let uu___584_5941 =
                                                         act  in
                                                       let uu____5942 =
                                                         FStar_Syntax_Subst.subst_binders
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_params
                                                          in
                                                       let uu____5943 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____5944 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___584_5941.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___584_5941.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = uvs;
                                                         FStar_Syntax_Syntax.action_params
                                                           = uu____5942;
                                                         FStar_Syntax_Syntax.action_defn
                                                           = uu____5943;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____5944
                                                       }  in
                                                     (uu____5939, uu____5940))
                                               in
                                            match uu____5902 with
                                            | (env3,act1) ->
                                                let act_typ =
                                                  let uu____5948 =
                                                    let uu____5949 =
                                                      FStar_Syntax_Subst.compress
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                       in
                                                    uu____5949.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____5948 with
                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                      (bs,c) ->
                                                      let c1 =
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                          c
                                                         in
                                                      let uu____5975 =
                                                        FStar_Ident.lid_equals
                                                          c1.FStar_Syntax_Syntax.effect_name
                                                          ed2.FStar_Syntax_Syntax.mname
                                                         in
                                                      if uu____5975
                                                      then
                                                        let uu____5978 =
                                                          let uu____5981 =
                                                            let uu____5982 =
                                                              let uu____5983
                                                                =
                                                                FStar_List.hd
                                                                  c1.FStar_Syntax_Syntax.effect_args
                                                                 in
                                                              FStar_Pervasives_Native.fst
                                                                uu____5983
                                                               in
                                                            mk_repr'
                                                              c1.FStar_Syntax_Syntax.result_typ
                                                              uu____5982
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total
                                                            uu____5981
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          bs uu____5978
                                                      else
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                  | uu____6006 ->
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                   in
                                                let uu____6007 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env3 act_typ
                                                   in
                                                (match uu____6007 with
                                                 | (act_typ1,uu____6015,g_t)
                                                     ->
                                                     let env' =
                                                       let uu___601_6018 =
                                                         FStar_TypeChecker_Env.set_expected_typ
                                                           env3 act_typ1
                                                          in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.is_pattern
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.is_pattern);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           = false;
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.lax);
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___601_6018.FStar_TypeChecker_Env.nbe)
                                                       }  in
                                                     ((let uu____6021 =
                                                         FStar_TypeChecker_Env.debug
                                                           env3
                                                           (FStar_Options.Other
                                                              "ED")
                                                          in
                                                       if uu____6021
                                                       then
                                                         let uu____6025 =
                                                           FStar_Ident.text_of_lid
                                                             act1.FStar_Syntax_Syntax.action_name
                                                            in
                                                         let uu____6027 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____6029 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act_typ1
                                                            in
                                                         FStar_Util.print3
                                                           "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                           uu____6025
                                                           uu____6027
                                                           uu____6029
                                                       else ());
                                                      (let uu____6034 =
                                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                           env'
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       match uu____6034 with
                                                       | (act_defn,uu____6042,g_a)
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
                                                           let uu____6046 =
                                                             let act_typ3 =
                                                               FStar_Syntax_Subst.compress
                                                                 act_typ2
                                                                in
                                                             match act_typ3.FStar_Syntax_Syntax.n
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____6082
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c
                                                                    in
                                                                 (match uu____6082
                                                                  with
                                                                  | (bs1,uu____6094)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____6101
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____6101
                                                                     in
                                                                    let uu____6104
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____6104
                                                                    with
                                                                    | 
                                                                    (k1,uu____6118,g)
                                                                    ->
                                                                    (k1, g)))
                                                             | uu____6122 ->
                                                                 let uu____6123
                                                                   =
                                                                   let uu____6129
                                                                    =
                                                                    let uu____6131
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____6133
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____6131
                                                                    uu____6133
                                                                     in
                                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____6129)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____6123
                                                                   act_defn1.FStar_Syntax_Syntax.pos
                                                              in
                                                           (match uu____6046
                                                            with
                                                            | (expected_k,g_k)
                                                                ->
                                                                let g =
                                                                  FStar_TypeChecker_Rel.teq
                                                                    env3
                                                                    act_typ2
                                                                    expected_k
                                                                   in
                                                                ((let uu____6151
                                                                    =
                                                                    let uu____6152
                                                                    =
                                                                    let uu____6153
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____6153
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____6152
                                                                     in
                                                                  FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env3
                                                                    uu____6151);
                                                                 (let act_typ3
                                                                    =
                                                                    let uu____6155
                                                                    =
                                                                    let uu____6156
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____6156.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____6155
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____6181
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____6181
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____6188
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____6188
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____6208
                                                                    =
                                                                    let uu____6209
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____6209]
                                                                     in
                                                                    let uu____6210
                                                                    =
                                                                    let uu____6221
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____6221]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6208;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6210;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____6246
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____6246))
                                                                    | 
                                                                    uu____6249
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                  let uu____6251
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env3
                                                                    act_defn1
                                                                    else
                                                                    (let uu____6273
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____6273))
                                                                     in
                                                                  match uu____6251
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
                                                                    let uu___651_6292
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___651_6292.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___651_6292.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___651_6292.FStar_Syntax_Syntax.action_params);
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
                                          (let uu____6301 =
                                             FStar_Syntax_Util.is_unknown
                                               (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                              in
                                           Prims.op_Negation uu____6301)
                                        then
                                          (let repr =
                                             let uu____6304 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             match uu____6304 with
                                             | (t,uu____6310) ->
                                                 let expected_k =
                                                   let uu____6314 =
                                                     let uu____6323 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     [uu____6323]  in
                                                   let uu____6342 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6314 uu____6342
                                                    in
                                                 ((let uu____6346 =
                                                     FStar_TypeChecker_Env.debug
                                                       env2
                                                       (FStar_Options.Other
                                                          "ED")
                                                      in
                                                   if uu____6346
                                                   then
                                                     let uu____6350 =
                                                       FStar_Syntax_Print.term_to_string
                                                         (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                                        in
                                                     let uu____6352 =
                                                       FStar_Syntax_Print.term_to_string
                                                         expected_k
                                                        in
                                                     FStar_Util.print2
                                                       "About to check repr=%s\nat type %s\n"
                                                       uu____6350 uu____6352
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
                                             let uu____6366 =
                                               let uu____6373 =
                                                 let uu____6374 =
                                                   let uu____6391 =
                                                     let uu____6402 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____6402]  in
                                                   (repr1, uu____6391)  in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6374
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____6373
                                                in
                                             uu____6366
                                               FStar_Pervasives_Native.None
                                               FStar_Range.dummyRange
                                              in
                                           let mk_repr a1 =
                                             let uu____6447 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a1
                                                in
                                             mk_repr' uu____6447  in
                                           let destruct_repr t =
                                             let uu____6462 =
                                               let uu____6463 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____6463.FStar_Syntax_Syntax.n
                                                in
                                             match uu____6462 with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____6474,(t1,uu____6476)::
                                                  (wp,uu____6478)::[])
                                                 -> (t1, wp)
                                             | uu____6537 ->
                                                 failwith
                                                   "Unexpected repr type"
                                              in
                                           let bind_repr =
                                             let r =
                                               let uu____6549 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_0
                                                   FStar_Syntax_Syntax.delta_constant
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_All.pipe_right
                                                 uu____6549
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                in
                                             let uu____6550 =
                                               fresh_effect_signature ()  in
                                             match uu____6550 with
                                             | (b,wp_b) ->
                                                 let x_a =
                                                   let uu____6564 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "x_a"
                                                     FStar_Pervasives_Native.None
                                                     uu____6564
                                                    in
                                                 let expected_k =
                                                   let uu____6569 =
                                                     let uu____6578 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6585 =
                                                       let uu____6594 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           b
                                                          in
                                                       let uu____6601 =
                                                         let uu____6610 =
                                                           let uu____6617 =
                                                             mk_repr a  in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____6617
                                                            in
                                                         let uu____6618 =
                                                           let uu____6627 =
                                                             let uu____6634 =
                                                               let uu____6635
                                                                 =
                                                                 let uu____6644
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_binder
                                                                    x_a
                                                                    in
                                                                 [uu____6644]
                                                                  in
                                                               let uu____6663
                                                                 =
                                                                 let uu____6666
                                                                   =
                                                                   mk_repr b
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Syntax.mk_Total
                                                                   uu____6666
                                                                  in
                                                               FStar_Syntax_Util.arrow
                                                                 uu____6635
                                                                 uu____6663
                                                                in
                                                             FStar_Syntax_Syntax.null_binder
                                                               uu____6634
                                                              in
                                                           [uu____6627]  in
                                                         uu____6610 ::
                                                           uu____6618
                                                          in
                                                       uu____6594 ::
                                                         uu____6601
                                                        in
                                                     uu____6578 :: uu____6585
                                                      in
                                                   let uu____6699 =
                                                     let uu____6702 =
                                                       mk_repr b  in
                                                     FStar_Syntax_Syntax.mk_Total
                                                       uu____6702
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6569 uu____6699
                                                    in
                                                 ((let uu____6704 =
                                                     FStar_TypeChecker_Env.debug
                                                       env2
                                                       (FStar_Options.Other
                                                          "ED")
                                                      in
                                                   if uu____6704
                                                   then
                                                     let uu____6708 =
                                                       FStar_Syntax_Print.term_to_string
                                                         expected_k
                                                        in
                                                     FStar_Util.print1
                                                       "About to check expected_k %s\n"
                                                       uu____6708
                                                   else ());
                                                  (let uu____6713 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env2 expected_k
                                                      in
                                                   match uu____6713 with
                                                   | (expected_k1,uu____6721,uu____6722)
                                                       ->
                                                       ((let uu____6724 =
                                                           FStar_TypeChecker_Env.debug
                                                             env2
                                                             (FStar_Options.Other
                                                                "ED")
                                                            in
                                                         if uu____6724
                                                         then
                                                           let uu____6728 =
                                                             FStar_Syntax_Print.term_to_string
                                                               (FStar_Pervasives_Native.snd
                                                                  (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind)
                                                              in
                                                           let uu____6734 =
                                                             FStar_Syntax_Print.term_to_string
                                                               expected_k1
                                                              in
                                                           FStar_Util.print2
                                                             "About to check bind=%s\n\n, at type %s\n"
                                                             uu____6728
                                                             uu____6734
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
                                                         (let uu____6754 =
                                                            FStar_TypeChecker_Env.debug
                                                              env3
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____6754
                                                          then
                                                            let uu____6758 =
                                                              FStar_Syntax_Print.tscheme_to_string
                                                                br
                                                               in
                                                            let uu____6760 =
                                                              FStar_Syntax_Print.term_to_string
                                                                expected_k1
                                                               in
                                                            FStar_Util.print2
                                                              "After checking bind_repr is %s\nexpected_k is %s\n"
                                                              uu____6758
                                                              uu____6760
                                                          else ());
                                                         br))))
                                              in
                                           let return_repr =
                                             let x_a =
                                               let uu____6767 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   a
                                                  in
                                               FStar_Syntax_Syntax.gen_bv
                                                 "x_a"
                                                 FStar_Pervasives_Native.None
                                                 uu____6767
                                                in
                                             let res = mk_repr a  in
                                             let expected_k =
                                               let uu____6775 =
                                                 let uu____6784 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     a
                                                    in
                                                 let uu____6791 =
                                                   let uu____6800 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       x_a
                                                      in
                                                   [uu____6800]  in
                                                 uu____6784 :: uu____6791  in
                                               let uu____6825 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   res
                                                  in
                                               FStar_Syntax_Util.arrow
                                                 uu____6775 uu____6825
                                                in
                                             let uu____6828 =
                                               FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                 env2 expected_k
                                                in
                                             match uu____6828 with
                                             | (expected_k1,uu____6836,uu____6837)
                                                 ->
                                                 let env3 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env2
                                                     (FStar_Pervasives_Native.snd
                                                        (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret).FStar_Syntax_Syntax.pos
                                                    in
                                                 let uu____6843 =
                                                   check_and_gen' env3
                                                     (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                                     expected_k1
                                                    in
                                                 (match uu____6843 with
                                                  | (univs1,repr1) ->
                                                      (match univs1 with
                                                       | [] -> ([], repr1)
                                                       | uu____6866 ->
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
                                    match uu____4920 with
                                    | (repr,bind_repr,return_repr,actions) ->
                                        let t0 =
                                          let uu____6894 =
                                            FStar_Syntax_Syntax.mk_Total
                                              signature1
                                             in
                                          FStar_Syntax_Util.arrow
                                            ed2.FStar_Syntax_Syntax.binders
                                            uu____6894
                                           in
                                        let uu____6897 =
                                          let uu____6902 =
                                            FStar_TypeChecker_Util.generalize_universes
                                              env0 t0
                                             in
                                          match uu____6902 with
                                          | (gen_univs,t) ->
                                              (match annotated_univ_names
                                               with
                                               | [] -> (gen_univs, t)
                                               | uu____6921 ->
                                                   let uu____6924 =
                                                     ((FStar_List.length
                                                         gen_univs)
                                                        =
                                                        (FStar_List.length
                                                           annotated_univ_names))
                                                       &&
                                                       (FStar_List.forall2
                                                          (fun u1  ->
                                                             fun u2  ->
                                                               let uu____6931
                                                                 =
                                                                 FStar_Syntax_Syntax.order_univ_name
                                                                   u1 u2
                                                                  in
                                                               uu____6931 =
                                                                 (Prims.parse_int "0"))
                                                          gen_univs
                                                          annotated_univ_names)
                                                      in
                                                   if uu____6924
                                                   then (gen_univs, t)
                                                   else
                                                     (let uu____6942 =
                                                        let uu____6948 =
                                                          let uu____6950 =
                                                            FStar_Util.string_of_int
                                                              (FStar_List.length
                                                                 annotated_univ_names)
                                                             in
                                                          let uu____6952 =
                                                            FStar_Util.string_of_int
                                                              (FStar_List.length
                                                                 gen_univs)
                                                             in
                                                          FStar_Util.format2
                                                            "Expected an effect definition with %s universes; but found %s"
                                                            uu____6950
                                                            uu____6952
                                                           in
                                                        (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                          uu____6948)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____6942
                                                        signature1.FStar_Syntax_Syntax.pos))
                                           in
                                        (match uu____6897 with
                                         | (univs1,t) ->
                                             let signature2 =
                                               let uu____6963 =
                                                 let uu____6976 =
                                                   let uu____6977 =
                                                     FStar_Syntax_Subst.compress
                                                       t
                                                      in
                                                   uu____6977.FStar_Syntax_Syntax.n
                                                    in
                                                 (effect_params, uu____6976)
                                                  in
                                               match uu____6963 with
                                               | ([],uu____6988) -> t
                                               | (uu____7003,FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____7004,c)) ->
                                                   FStar_Syntax_Util.comp_result
                                                     c
                                               | uu____7042 ->
                                                   failwith
                                                     "Impossible : t is an arrow"
                                                in
                                             let close1 n1 ts =
                                               let ts1 =
                                                 let uu____7070 =
                                                   FStar_Syntax_Subst.close_tscheme
                                                     effect_params ts
                                                    in
                                                 FStar_Syntax_Subst.close_univ_vars_tscheme
                                                   univs1 uu____7070
                                                  in
                                               let m =
                                                 FStar_List.length
                                                   (FStar_Pervasives_Native.fst
                                                      ts1)
                                                  in
                                               (let uu____7077 =
                                                  ((n1 >=
                                                      (Prims.parse_int "0"))
                                                     &&
                                                     (let uu____7081 =
                                                        FStar_Syntax_Util.is_unknown
                                                          (FStar_Pervasives_Native.snd
                                                             ts1)
                                                         in
                                                      Prims.op_Negation
                                                        uu____7081))
                                                    && (m <> n1)
                                                   in
                                                if uu____7077
                                                then
                                                  let err_msg uu____7095 =
                                                    let error =
                                                      if m < n1
                                                      then
                                                        "not universe-polymorphic enough"
                                                      else
                                                        "too universe-polymorphic"
                                                       in
                                                    let uu____7104 =
                                                      FStar_Util.string_of_int
                                                        m
                                                       in
                                                    let uu____7106 =
                                                      FStar_Util.string_of_int
                                                        n1
                                                       in
                                                    let uu____7108 =
                                                      FStar_Syntax_Print.tscheme_to_string
                                                        ts1
                                                       in
                                                    FStar_Util.format4
                                                      "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                      error uu____7104
                                                      uu____7106 uu____7108
                                                     in
                                                  let uu____7111 =
                                                    let uu____7117 =
                                                      err_msg ()  in
                                                    (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                      uu____7117)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____7111
                                                    (FStar_Pervasives_Native.snd
                                                       ts1).FStar_Syntax_Syntax.pos
                                                else ());
                                               ts1  in
                                             let close_action act =
                                               let uu____7132 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               match uu____7132 with
                                               | (univs2,defn) ->
                                                   let uu____7148 =
                                                     close1
                                                       (~-
                                                          (Prims.parse_int "1"))
                                                       ((act.FStar_Syntax_Syntax.action_univs),
                                                         (act.FStar_Syntax_Syntax.action_typ))
                                                      in
                                                   (match uu____7148 with
                                                    | (univs',typ) ->
                                                        let uu___762_7165 =
                                                          act  in
                                                        {
                                                          FStar_Syntax_Syntax.action_name
                                                            =
                                                            (uu___762_7165.FStar_Syntax_Syntax.action_name);
                                                          FStar_Syntax_Syntax.action_unqualified_name
                                                            =
                                                            (uu___762_7165.FStar_Syntax_Syntax.action_unqualified_name);
                                                          FStar_Syntax_Syntax.action_univs
                                                            = univs2;
                                                          FStar_Syntax_Syntax.action_params
                                                            =
                                                            (uu___762_7165.FStar_Syntax_Syntax.action_params);
                                                          FStar_Syntax_Syntax.action_defn
                                                            = defn;
                                                          FStar_Syntax_Syntax.action_typ
                                                            = typ
                                                        })
                                                in
                                             let ed3 =
                                               let uu___765_7168 = ed2  in
                                               let uu____7169 =
                                                 let uu____7170 =
                                                   close1
                                                     (Prims.parse_int "0")
                                                     return_wp
                                                    in
                                                 let uu____7172 =
                                                   close1
                                                     (Prims.parse_int "1")
                                                     bind_wp
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.monad_m
                                                     =
                                                     FStar_Syntax_Syntax.tun;
                                                   FStar_Syntax_Syntax.monad_ret
                                                     = uu____7170;
                                                   FStar_Syntax_Syntax.monad_bind
                                                     = uu____7172
                                                 }  in
                                               let uu____7174 =
                                                 close1 (Prims.parse_int "0")
                                                   if_then_else1
                                                  in
                                               let uu____7176 =
                                                 close1 (Prims.parse_int "0")
                                                   ite_wp
                                                  in
                                               let uu____7178 =
                                                 close1 (Prims.parse_int "0")
                                                   stronger
                                                  in
                                               let uu____7180 =
                                                 close1 (Prims.parse_int "1")
                                                   close_wp
                                                  in
                                               let uu____7182 =
                                                 close1 (Prims.parse_int "0")
                                                   assert_p
                                                  in
                                               let uu____7184 =
                                                 close1 (Prims.parse_int "0")
                                                   assume_p
                                                  in
                                               let uu____7186 =
                                                 close1 (Prims.parse_int "0")
                                                   null_wp
                                                  in
                                               let uu____7188 =
                                                 close1 (Prims.parse_int "0")
                                                   trivial_wp
                                                  in
                                               let uu____7190 =
                                                 let uu____7191 =
                                                   let uu____7192 =
                                                     close1
                                                       (Prims.parse_int "0")
                                                       ([], repr)
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____7192
                                                    in
                                                 let uu____7210 =
                                                   close1
                                                     (Prims.parse_int "0")
                                                     return_repr
                                                    in
                                                 let uu____7212 =
                                                   close1
                                                     (Prims.parse_int "1")
                                                     bind_repr
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.monad_m
                                                     = uu____7191;
                                                   FStar_Syntax_Syntax.monad_ret
                                                     = uu____7210;
                                                   FStar_Syntax_Syntax.monad_bind
                                                     = uu____7212
                                                 }  in
                                               let uu____7214 =
                                                 FStar_Util.map_opt interp
                                                   (close1
                                                      (Prims.parse_int "0"))
                                                  in
                                               let uu____7218 =
                                                 FStar_Util.map_opt mrelation
                                                   (close1
                                                      (Prims.parse_int "0"))
                                                  in
                                               let uu____7222 =
                                                 FStar_List.map close_action
                                                   actions
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.cattributes
                                                   =
                                                   (uu___765_7168.FStar_Syntax_Syntax.cattributes);
                                                 FStar_Syntax_Syntax.mname =
                                                   (uu___765_7168.FStar_Syntax_Syntax.mname);
                                                 FStar_Syntax_Syntax.univs =
                                                   univs1;
                                                 FStar_Syntax_Syntax.binders
                                                   = effect_params;
                                                 FStar_Syntax_Syntax.spec =
                                                   uu____7169;
                                                 FStar_Syntax_Syntax.signature
                                                   = signature2;
                                                 FStar_Syntax_Syntax.if_then_else
                                                   = uu____7174;
                                                 FStar_Syntax_Syntax.ite_wp =
                                                   uu____7176;
                                                 FStar_Syntax_Syntax.stronger
                                                   = uu____7178;
                                                 FStar_Syntax_Syntax.close_wp
                                                   = uu____7180;
                                                 FStar_Syntax_Syntax.assert_p
                                                   = uu____7182;
                                                 FStar_Syntax_Syntax.assume_p
                                                   = uu____7184;
                                                 FStar_Syntax_Syntax.null_wp
                                                   = uu____7186;
                                                 FStar_Syntax_Syntax.trivial
                                                   = uu____7188;
                                                 FStar_Syntax_Syntax.repr =
                                                   uu____7190;
                                                 FStar_Syntax_Syntax.elaborated
                                                   =
                                                   (uu___765_7168.FStar_Syntax_Syntax.elaborated);
                                                 FStar_Syntax_Syntax.spec_dm4f
                                                   =
                                                   (uu___765_7168.FStar_Syntax_Syntax.spec_dm4f);
                                                 FStar_Syntax_Syntax.interp =
                                                   uu____7214;
                                                 FStar_Syntax_Syntax.mrelation
                                                   = uu____7218;
                                                 FStar_Syntax_Syntax.actions
                                                   = uu____7222;
                                                 FStar_Syntax_Syntax.eff_attrs
                                                   =
                                                   (uu___765_7168.FStar_Syntax_Syntax.eff_attrs)
                                               }  in
                                             ed3)))))))))
  
let tc_lex_t :
  'Auu____7236 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____7236 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____7271 = FStar_List.hd ses  in
            uu____7271.FStar_Syntax_Syntax.sigrng  in
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
           | uu____7276 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____7282,[],t,uu____7284,uu____7285);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____7287;
               FStar_Syntax_Syntax.sigattrs = uu____7288;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____7290,_t_top,_lex_t_top,_7324,uu____7293);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____7295;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____7296;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____7298,_t_cons,_lex_t_cons,_7332,uu____7301);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____7303;
                 FStar_Syntax_Syntax.sigattrs = uu____7304;_}::[]
               when
               ((_7324 = (Prims.parse_int "0")) &&
                  (_7332 = (Prims.parse_int "0")))
                 &&
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
                 let uu____7357 =
                   let uu____7364 =
                     let uu____7365 =
                       let uu____7372 =
                         let uu____7375 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____7375
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____7372, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____7365  in
                   FStar_Syntax_Syntax.mk uu____7364  in
                 uu____7357 FStar_Pervasives_Native.None r1  in
               let lex_top_t1 =
                 FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t  in
               let dc_lextop =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_top1, [utop], lex_top_t1,
                          FStar_Parser_Const.lex_t_lid,
                          (Prims.parse_int "0"), []));
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
                   let uu____7390 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7390
                    in
                 let hd1 =
                   let uu____7392 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7392
                    in
                 let tl1 =
                   let uu____7394 =
                     let uu____7395 =
                       let uu____7402 =
                         let uu____7403 =
                           let uu____7410 =
                             let uu____7413 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____7413
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____7410, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____7403  in
                       FStar_Syntax_Syntax.mk uu____7402  in
                     uu____7395 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7394
                    in
                 let res =
                   let uu____7419 =
                     let uu____7426 =
                       let uu____7427 =
                         let uu____7434 =
                           let uu____7437 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____7437
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____7434,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____7427  in
                     FStar_Syntax_Syntax.mk uu____7426  in
                   uu____7419 FStar_Pervasives_Native.None r2  in
                 let uu____7440 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____7440
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
                          FStar_Parser_Const.lex_t_lid,
                          (Prims.parse_int "0"), []));
                   FStar_Syntax_Syntax.sigrng = r2;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let uu____7479 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____7479;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____7484 ->
               let err_msg =
                 let uu____7489 =
                   let uu____7491 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____7491  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____7489
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
    fun uu____7516  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____7516 with
          | (uvs,t) ->
              let uu____7529 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____7529 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____7541 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____7541 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____7559 =
                        let uu____7562 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____7562
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____7559)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7585 =
          let uu____7586 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7586 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7585 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7611 =
          let uu____7612 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7612 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7611 r
  
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
          (let uu____7661 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____7661
           then
             let uu____7664 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____7664
           else ());
          (let uu____7669 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____7669 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____7700 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____7700 FStar_List.flatten  in
               ((let uu____7714 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____7717 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____7717)
                    in
                 if uu____7714
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
                           let uu____7733 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____7743,uu____7744,uu____7745,uu____7746,uu____7747)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____7756 -> failwith "Impossible!"  in
                           match uu____7733 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Inductive type "
                                      (Prims.op_Hat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____7775 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____7785,uu____7786,ty_lid,uu____7788,uu____7789)
                               -> (data_lid, ty_lid)
                           | uu____7796 -> failwith "Impossible"  in
                         match uu____7775 with
                         | (data_lid,ty_lid) ->
                             let uu____7804 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____7807 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____7807)
                                in
                             if uu____7804
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Exception "
                                      (Prims.op_Hat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____7821 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____7826,uu____7827,uu____7828,uu____7829,uu____7830)
                         -> lid
                     | uu____7839 -> failwith "Impossible"  in
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
                   let uu____7857 =
                     (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____7857
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
          let pop1 uu____7932 =
            let uu____7933 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___935_7943  ->
               match () with
               | () ->
                   let uu____7950 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____7950 (fun r  -> pop1 (); r)) ()
          with | uu___934_7981 -> (pop1 (); FStar_Exn.raise uu___934_7981)
  
let (z3_reset_options :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun en  ->
    let env =
      let uu____8002 = FStar_Options.using_facts_from ()  in
      FStar_TypeChecker_Env.set_proof_ns uu____8002 en  in
    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh (); env
  
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
      | uu____8306 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____8364 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____8364 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____8389 .
    'Auu____8389 FStar_Pervasives_Native.option -> 'Auu____8389 Prims.list
  =
  fun uu___0_8398  ->
    match uu___0_8398 with
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
            let uu____8478 = collect1 tl1  in
            (match uu____8478 with
             | [] -> [(hd1, (Prims.parse_int "1"))]
             | (h,n1)::t ->
                 if h = hd1
                 then (h, (n1 + (Prims.parse_int "1"))) :: t
                 else (hd1, (Prims.parse_int "1")) :: (h, n1) :: t)
         in
      let summ l = collect1 l  in
      let l11 = summ l1  in
      let l21 = summ l2  in
      let rec aux l12 l22 =
        match (l12, l22) with
        | ([],[]) -> FStar_Pervasives_Native.None
        | ((e,n1)::uu____8716,[]) ->
            FStar_Pervasives_Native.Some (e, n1, (Prims.parse_int "0"))
        | ([],(e,n1)::uu____8772) ->
            FStar_Pervasives_Native.Some (e, (Prims.parse_int "0"), n1)
        | ((hd1,n1)::tl1,(hd2,n2)::tl2) when hd1 <> hd2 ->
            if hd1 < hd2
            then
              FStar_Pervasives_Native.Some (hd1, n1, (Prims.parse_int "0"))
            else
              if hd1 > hd2
              then
                FStar_Pervasives_Native.Some (hd2, (Prims.parse_int "0"), n2)
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
          let uu____8983 =
            let uu____8985 = FStar_Options.ide ()  in
            Prims.op_Negation uu____8985  in
          if uu____8983
          then
            let uu____8988 =
              let uu____8993 = FStar_TypeChecker_Env.dsenv env  in
              let uu____8994 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____8993 uu____8994  in
            (match uu____8988 with
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
                              let uu____9027 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____9028 =
                                let uu____9034 =
                                  let uu____9036 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____9038 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____9036 uu____9038
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____9034)
                                 in
                              FStar_Errors.log_issue uu____9027 uu____9028
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____9045 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____9046 =
                                   let uu____9052 =
                                     let uu____9054 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____9054
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____9052)
                                    in
                                 FStar_Errors.log_issue uu____9045 uu____9046)
                              else ())
                         else ())))
          else ()
      | uu____9064 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____9109 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____9137 ->
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
             let uu____9197 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____9197
             then
               let ses1 =
                 let uu____9205 =
                   let uu____9206 =
                     let uu____9207 =
                       tc_inductive
                         (let uu___1070_9216 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1070_9216.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1070_9216.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1070_9216.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1070_9216.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1070_9216.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1070_9216.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1070_9216.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1070_9216.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1070_9216.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1070_9216.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1070_9216.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1070_9216.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1070_9216.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1070_9216.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1070_9216.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1070_9216.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1070_9216.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1070_9216.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1070_9216.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1070_9216.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1070_9216.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___1070_9216.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1070_9216.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1070_9216.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1070_9216.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1070_9216.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1070_9216.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1070_9216.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1070_9216.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1070_9216.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1070_9216.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1070_9216.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1070_9216.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1070_9216.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1070_9216.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1070_9216.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1070_9216.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1070_9216.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1070_9216.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1070_9216.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1070_9216.FStar_TypeChecker_Env.nbe)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____9207
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____9206
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____9205
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____9230 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____9230
                 then
                   let uu____9235 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1074_9239 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1074_9239.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1074_9239.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1074_9239.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1074_9239.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____9235
                 else ());
                ses1)
             else ses  in
           let uu____9249 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____9249 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___1081_9273 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1081_9273.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1081_9273.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1081_9273.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1081_9273.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let forfree =
             let uu____9287 =
               let uu____9288 =
                 FStar_Syntax_Subst.compress
                   (ne.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                  in
               uu____9288.FStar_Syntax_Syntax.n  in
             match uu____9287 with
             | FStar_Syntax_Syntax.Tm_unknown  -> false
             | uu____9293 ->
                 Prims.op_Negation ne.FStar_Syntax_Syntax.elaborated
              in
           if forfree
           then
             ((let uu____9306 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____9306
               then FStar_Util.print_string "Beginning DM4F run\n"
               else ());
              (let uu____9313 = cps_and_elaborate_ed env0 ne  in
               match uu____9313 with
               | (ses,ne1,lift_from_pure_opt) ->
                   let ne2 =
                     let uu___1099_9346 = ne1  in
                     {
                       FStar_Syntax_Syntax.cattributes =
                         (uu___1099_9346.FStar_Syntax_Syntax.cattributes);
                       FStar_Syntax_Syntax.mname =
                         (uu___1099_9346.FStar_Syntax_Syntax.mname);
                       FStar_Syntax_Syntax.univs =
                         (uu___1099_9346.FStar_Syntax_Syntax.univs);
                       FStar_Syntax_Syntax.binders =
                         (uu___1099_9346.FStar_Syntax_Syntax.binders);
                       FStar_Syntax_Syntax.spec =
                         (uu___1099_9346.FStar_Syntax_Syntax.spec);
                       FStar_Syntax_Syntax.signature =
                         (uu___1099_9346.FStar_Syntax_Syntax.signature);
                       FStar_Syntax_Syntax.if_then_else =
                         (uu___1099_9346.FStar_Syntax_Syntax.if_then_else);
                       FStar_Syntax_Syntax.ite_wp =
                         (uu___1099_9346.FStar_Syntax_Syntax.ite_wp);
                       FStar_Syntax_Syntax.stronger =
                         (uu___1099_9346.FStar_Syntax_Syntax.stronger);
                       FStar_Syntax_Syntax.close_wp =
                         (uu___1099_9346.FStar_Syntax_Syntax.close_wp);
                       FStar_Syntax_Syntax.assert_p =
                         (uu___1099_9346.FStar_Syntax_Syntax.assert_p);
                       FStar_Syntax_Syntax.assume_p =
                         (uu___1099_9346.FStar_Syntax_Syntax.assume_p);
                       FStar_Syntax_Syntax.null_wp =
                         (uu___1099_9346.FStar_Syntax_Syntax.null_wp);
                       FStar_Syntax_Syntax.trivial =
                         (uu___1099_9346.FStar_Syntax_Syntax.trivial);
                       FStar_Syntax_Syntax.repr =
                         (uu___1099_9346.FStar_Syntax_Syntax.repr);
                       FStar_Syntax_Syntax.elaborated = true;
                       FStar_Syntax_Syntax.spec_dm4f =
                         (uu___1099_9346.FStar_Syntax_Syntax.spec_dm4f);
                       FStar_Syntax_Syntax.interp =
                         (uu___1099_9346.FStar_Syntax_Syntax.interp);
                       FStar_Syntax_Syntax.mrelation =
                         (uu___1099_9346.FStar_Syntax_Syntax.mrelation);
                       FStar_Syntax_Syntax.actions =
                         (uu___1099_9346.FStar_Syntax_Syntax.actions);
                       FStar_Syntax_Syntax.eff_attrs =
                         (uu___1099_9346.FStar_Syntax_Syntax.eff_attrs)
                     }  in
                   let effect_and_lift_ses =
                     match lift_from_pure_opt with
                     | FStar_Pervasives_Native.Some lift ->
                         [(let uu___1104_9355 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne2);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1104_9355.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___1104_9355.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1104_9355.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1104_9355.FStar_Syntax_Syntax.sigattrs)
                           });
                         lift]
                     | FStar_Pervasives_Native.None  ->
                         [(let uu___1107_9357 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne2);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1107_9357.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___1107_9357.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1107_9357.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1107_9357.FStar_Syntax_Syntax.sigattrs)
                           })]
                      in
                   ([], (FStar_List.append ses effect_and_lift_ses), env0)))
           else
             (let ne1 =
                let uu____9365 =
                  (FStar_Options.use_two_phase_tc ()) &&
                    (FStar_TypeChecker_Env.should_verify env)
                   in
                if uu____9365
                then
                  let ne1 =
                    let uu____9369 =
                      let uu____9370 =
                        let uu____9371 =
                          tc_eff_decl
                            (let uu___1111_9373 = env  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1111_9373.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1111_9373.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1111_9373.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1111_9373.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1111_9373.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1111_9373.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1111_9373.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1111_9373.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1111_9373.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1111_9373.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___1111_9373.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1111_9373.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1111_9373.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1111_9373.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___1111_9373.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___1111_9373.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1111_9373.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___1111_9373.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1111_9373.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1111_9373.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1111_9373.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 = true;
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1111_9373.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1111_9373.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1111_9373.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1111_9373.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1111_9373.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1111_9373.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1111_9373.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1111_9373.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1111_9373.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1111_9373.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1111_9373.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1111_9373.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1111_9373.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1111_9373.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1111_9373.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___1111_9373.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1111_9373.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1111_9373.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1111_9373.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1111_9373.FStar_TypeChecker_Env.nbe)
                             }) se ne
                           in
                        FStar_All.pipe_right uu____9371
                          (fun ne1  ->
                             let uu___1114_9379 = se  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___1114_9379.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___1114_9379.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___1114_9379.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___1114_9379.FStar_Syntax_Syntax.sigattrs)
                             })
                         in
                      FStar_All.pipe_right uu____9370
                        (FStar_TypeChecker_Normalize.elim_uvars env)
                       in
                    FStar_All.pipe_right uu____9369
                      FStar_Syntax_Util.eff_decl_of_new_effect
                     in
                  ((let uu____9381 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "TwoPhases")
                       in
                    if uu____9381
                    then
                      let uu____9386 =
                        FStar_Syntax_Print.sigelt_to_string
                          (let uu___1118_9390 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne1);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1118_9390.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___1118_9390.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1118_9390.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1118_9390.FStar_Syntax_Syntax.sigattrs)
                           })
                         in
                      FStar_Util.print1 "Effect decl after phase 1: %s\n"
                        uu____9386
                    else ());
                   ne1)
                else ne  in
              let ne2 = tc_eff_decl env se ne1  in
              let se1 =
                let uu___1123_9398 = se  in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_new_effect ne2);
                  FStar_Syntax_Syntax.sigrng =
                    (uu___1123_9398.FStar_Syntax_Syntax.sigrng);
                  FStar_Syntax_Syntax.sigquals =
                    (uu___1123_9398.FStar_Syntax_Syntax.sigquals);
                  FStar_Syntax_Syntax.sigmeta =
                    (uu___1123_9398.FStar_Syntax_Syntax.sigmeta);
                  FStar_Syntax_Syntax.sigattrs =
                    (uu___1123_9398.FStar_Syntax_Syntax.sigattrs)
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
           let uu____9406 =
             let uu____9413 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9413
              in
           (match uu____9406 with
            | (a,wp_a_src) ->
                let uu____9430 =
                  let uu____9437 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____9437
                   in
                (match uu____9430 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____9455 =
                         let uu____9458 =
                           let uu____9459 =
                             let uu____9466 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____9466)  in
                           FStar_Syntax_Syntax.NT uu____9459  in
                         [uu____9458]  in
                       FStar_Syntax_Subst.subst uu____9455 wp_b_tgt  in
                     let expected_k =
                       let uu____9474 =
                         let uu____9483 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____9490 =
                           let uu____9499 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____9499]  in
                         uu____9483 :: uu____9490  in
                       let uu____9524 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____9474 uu____9524  in
                     let repr_type eff_name a1 wp =
                       (let uu____9546 =
                          let uu____9548 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name
                             in
                          Prims.op_Negation uu____9548  in
                        if uu____9546
                        then
                          let uu____9551 =
                            let uu____9557 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____9557)
                             in
                          let uu____9561 =
                            FStar_TypeChecker_Env.get_range env  in
                          FStar_Errors.raise_error uu____9551 uu____9561
                        else ());
                       (let uu____9564 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name
                           in
                        match uu____9564 with
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
                            let uu____9601 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____9602 =
                              let uu____9609 =
                                let uu____9610 =
                                  let uu____9627 =
                                    let uu____9638 =
                                      FStar_Syntax_Syntax.as_arg a1  in
                                    let uu____9647 =
                                      let uu____9658 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____9658]  in
                                    uu____9638 :: uu____9647  in
                                  (repr, uu____9627)  in
                                FStar_Syntax_Syntax.Tm_app uu____9610  in
                              FStar_Syntax_Syntax.mk uu____9609  in
                            uu____9602 FStar_Pervasives_Native.None
                              uu____9601)
                        in
                     let uu____9703 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____9876 =
                             if
                               (FStar_List.length uvs) >
                                 (Prims.parse_int "0")
                             then
                               let uu____9887 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____9887 with
                               | (usubst,uvs1) ->
                                   let uu____9910 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____9911 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____9910, uu____9911)
                             else (env, lift_wp)  in
                           (match uu____9876 with
                            | (env1,lift_wp1) ->
                                let lift_wp2 =
                                  if
                                    (FStar_List.length uvs) =
                                      (Prims.parse_int "0")
                                  then check_and_gen env1 lift_wp1 expected_k
                                  else
                                    (let lift_wp2 =
                                       tc_check_trivial_guard env1 lift_wp1
                                         expected_k
                                        in
                                     let uu____9961 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____9961))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____10032 =
                             if
                               (FStar_List.length what) >
                                 (Prims.parse_int "0")
                             then
                               let uu____10047 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____10047 with
                               | (usubst,uvs) ->
                                   let uu____10072 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____10072)
                             else ([], lift)  in
                           (match uu____10032 with
                            | (uvs,lift1) ->
                                ((let uu____10108 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____10108
                                  then
                                    let uu____10112 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____10112
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____10118 =
                                    let uu____10125 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____10125 lift1
                                     in
                                  match uu____10118 with
                                  | (lift2,comp,uu____10150) ->
                                      let uu____10151 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____10151 with
                                       | (uu____10180,lift_wp,lift_elab) ->
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
                                               (Prims.parse_int "0")
                                           then
                                             let uu____10212 =
                                               let uu____10223 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10223
                                                in
                                             let uu____10240 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____10212, uu____10240)
                                           else
                                             (let uu____10269 =
                                                let uu____10280 =
                                                  let uu____10289 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____10289)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____10280
                                                 in
                                              let uu____10304 =
                                                let uu____10313 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____10313)  in
                                              (uu____10269, uu____10304))))))
                        in
                     (match uu____9703 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___1199_10387 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1199_10387.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1199_10387.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1199_10387.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1199_10387.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1199_10387.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1199_10387.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1199_10387.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1199_10387.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1199_10387.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1199_10387.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1199_10387.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1199_10387.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1199_10387.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1199_10387.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1199_10387.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1199_10387.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1199_10387.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1199_10387.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1199_10387.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1199_10387.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1199_10387.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1199_10387.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1199_10387.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1199_10387.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1199_10387.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1199_10387.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1199_10387.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1199_10387.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1199_10387.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1199_10387.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1199_10387.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1199_10387.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1199_10387.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1199_10387.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1199_10387.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1199_10387.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1199_10387.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1199_10387.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1199_10387.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1199_10387.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1199_10387.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1199_10387.FStar_TypeChecker_Env.nbe)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____10444 =
                                  let uu____10449 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____10449 with
                                  | (usubst,uvs1) ->
                                      let uu____10472 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____10473 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____10472, uu____10473)
                                   in
                                (match uu____10444 with
                                 | (env2,lift2) ->
                                     let uu____10486 =
                                       let uu____10493 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____10493
                                        in
                                     (match uu____10486 with
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
                                              let uu____10527 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____10528 =
                                                let uu____10535 =
                                                  let uu____10536 =
                                                    let uu____10553 =
                                                      let uu____10564 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____10573 =
                                                        let uu____10584 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____10584]  in
                                                      uu____10564 ::
                                                        uu____10573
                                                       in
                                                    (lift_wp1, uu____10553)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10536
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____10535
                                                 in
                                              uu____10528
                                                FStar_Pervasives_Native.None
                                                uu____10527
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____10632 =
                                              let uu____10641 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____10648 =
                                                let uu____10657 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____10664 =
                                                  let uu____10673 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____10673]  in
                                                uu____10657 :: uu____10664
                                                 in
                                              uu____10641 :: uu____10648  in
                                            let uu____10704 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____10632 uu____10704
                                             in
                                          let uu____10707 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____10707 with
                                           | (expected_k2,uu____10725,uu____10726)
                                               ->
                                               let lift3 =
                                                 if
                                                   (FStar_List.length uvs) =
                                                     (Prims.parse_int "0")
                                                 then
                                                   check_and_gen env2 lift2
                                                     expected_k2
                                                 else
                                                   (let lift3 =
                                                      tc_check_trivial_guard
                                                        env2 lift2
                                                        expected_k2
                                                       in
                                                    let uu____10750 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____10750))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____10766 =
                              let uu____10768 =
                                let uu____10770 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____10770
                                  FStar_List.length
                                 in
                              uu____10768 <> (Prims.parse_int "1")  in
                            if uu____10766
                            then
                              let uu____10793 =
                                let uu____10799 =
                                  let uu____10801 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____10803 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10805 =
                                    let uu____10807 =
                                      let uu____10809 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10809
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10807
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____10801 uu____10803 uu____10805
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____10799)
                                 in
                              FStar_Errors.raise_error uu____10793 r
                            else ());
                           (let uu____10836 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____10847 =
                                   let uu____10849 =
                                     let uu____10852 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____10852
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____10849
                                     FStar_List.length
                                    in
                                 uu____10847 <> (Prims.parse_int "1"))
                               in
                            if uu____10836
                            then
                              let uu____10907 =
                                let uu____10913 =
                                  let uu____10915 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____10917 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10919 =
                                    let uu____10921 =
                                      let uu____10923 =
                                        let uu____10926 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____10926
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10923
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10921
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____10915 uu____10917 uu____10919
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____10913)
                                 in
                              FStar_Errors.raise_error uu____10907 r
                            else ());
                           (let sub2 =
                              let uu___1236_10985 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___1236_10985.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___1236_10985.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___1239_10987 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___1239_10987.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___1239_10987.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___1239_10987.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___1239_10987.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let uu____11001 =
             if (FStar_List.length uvs) = (Prims.parse_int "0")
             then (env, uvs, tps, c)
             else
               (let uu____11029 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____11029 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____11060 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____11060 c  in
                    let uu____11069 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____11069, uvs1, tps1, c1))
              in
           (match uu____11001 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____11091 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____11091 with
                 | (tps2,c2) ->
                     let uu____11108 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____11108 with
                      | (tps3,env3,us) ->
                          let uu____11128 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____11128 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____11156)::uu____11157 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____11176 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____11184 =
                                   let uu____11186 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____11186  in
                                 if uu____11184
                                 then
                                   let uu____11189 =
                                     let uu____11195 =
                                       let uu____11197 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____11199 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____11197 uu____11199
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____11195)
                                      in
                                   FStar_Errors.raise_error uu____11189 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____11207 =
                                   let uu____11208 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____11208
                                    in
                                 match uu____11207 with
                                 | (uvs2,t) ->
                                     let uu____11239 =
                                       let uu____11244 =
                                         let uu____11257 =
                                           let uu____11258 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____11258.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____11257)  in
                                       match uu____11244 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____11273,c5)) -> ([], c5)
                                       | (uu____11315,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____11354 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____11239 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               (Prims.parse_int "1")
                                           then
                                             (let uu____11388 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____11388 with
                                              | (uu____11393,t1) ->
                                                  let uu____11395 =
                                                    let uu____11401 =
                                                      let uu____11403 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____11405 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____11409 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____11403
                                                        uu____11405
                                                        uu____11409
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____11401)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____11395 r)
                                           else ();
                                           (let se1 =
                                              let uu___1309_11416 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___1309_11416.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___1309_11416.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___1309_11416.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___1309_11416.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____11423,uu____11424,uu____11425) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_11430  ->
                   match uu___1_11430 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____11433 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____11439,uu____11440) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_11449  ->
                   match uu___1_11449 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____11452 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____11463 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____11463
             then
               let uu____11466 =
                 let uu____11472 =
                   let uu____11474 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____11474
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____11472)
                  in
               FStar_Errors.raise_error uu____11466 r
             else ());
            (let uu____11480 =
               let uu____11489 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____11489
               then
                 let uu____11500 =
                   tc_declare_typ
                     (let uu___1333_11503 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1333_11503.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1333_11503.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1333_11503.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1333_11503.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1333_11503.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1333_11503.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1333_11503.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1333_11503.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1333_11503.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1333_11503.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1333_11503.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1333_11503.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1333_11503.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1333_11503.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1333_11503.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1333_11503.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1333_11503.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1333_11503.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1333_11503.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1333_11503.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1333_11503.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1333_11503.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1333_11503.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1333_11503.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1333_11503.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1333_11503.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1333_11503.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1333_11503.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1333_11503.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1333_11503.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1333_11503.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1333_11503.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1333_11503.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1333_11503.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1333_11503.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1333_11503.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1333_11503.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1333_11503.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1333_11503.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1333_11503.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___1333_11503.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___1333_11503.FStar_TypeChecker_Env.nbe)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____11500 with
                 | (uvs1,t1) ->
                     ((let uu____11528 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____11528
                       then
                         let uu____11533 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____11535 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____11533 uu____11535
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____11480 with
             | (uvs1,t1) ->
                 let uu____11570 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____11570 with
                  | (uvs2,t2) ->
                      ([(let uu___1346_11600 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1346_11600.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1346_11600.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1346_11600.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1346_11600.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____11605 =
             let uu____11614 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____11614
             then
               let uu____11625 =
                 tc_assume
                   (let uu___1355_11628 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1355_11628.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1355_11628.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1355_11628.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1355_11628.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1355_11628.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1355_11628.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1355_11628.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1355_11628.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1355_11628.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1355_11628.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1355_11628.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1355_11628.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1355_11628.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1355_11628.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1355_11628.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1355_11628.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1355_11628.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1355_11628.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1355_11628.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1355_11628.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1355_11628.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___1355_11628.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1355_11628.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1355_11628.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1355_11628.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1355_11628.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1355_11628.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1355_11628.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1355_11628.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1355_11628.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1355_11628.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1355_11628.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1355_11628.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1355_11628.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1355_11628.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1355_11628.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1355_11628.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1355_11628.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1355_11628.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1355_11628.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1355_11628.FStar_TypeChecker_Env.nbe)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____11625 with
               | (uvs1,t1) ->
                   ((let uu____11654 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____11654
                     then
                       let uu____11659 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____11661 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____11659
                         uu____11661
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____11605 with
            | (uvs1,t1) ->
                let uu____11696 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____11696 with
                 | (uvs2,t2) ->
                     ([(let uu___1368_11726 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1368_11726.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1368_11726.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1368_11726.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1368_11726.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____11730 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____11730 with
            | (e1,c,g1) ->
                let uu____11750 =
                  let uu____11757 =
                    let uu____11760 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____11760  in
                  let uu____11761 =
                    let uu____11766 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____11766)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____11757 uu____11761
                   in
                (match uu____11750 with
                 | (e2,uu____11778,g) ->
                     ((let uu____11781 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____11781);
                      (let se1 =
                         let uu___1383_11783 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1383_11783.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1383_11783.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1383_11783.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1383_11783.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____11795 = FStar_Options.debug_any ()  in
             if uu____11795
             then
               let uu____11798 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____11800 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____11798
                 uu____11800
             else ());
            (let uu____11805 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____11805 with
             | (t1,uu____11823,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____11837 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____11837 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____11840 =
                              let uu____11846 =
                                let uu____11848 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____11850 =
                                  let uu____11852 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____11852
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____11848 uu____11850
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____11846)
                               in
                            FStar_Errors.raise_error uu____11840 r
                        | uu____11864 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___1404_11869 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1404_11869.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1404_11869.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1404_11869.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1404_11869.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1404_11869.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1404_11869.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1404_11869.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1404_11869.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1404_11869.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1404_11869.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1404_11869.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1404_11869.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1404_11869.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1404_11869.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1404_11869.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1404_11869.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1404_11869.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1404_11869.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1404_11869.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1404_11869.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___1404_11869.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1404_11869.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1404_11869.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1404_11869.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1404_11869.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1404_11869.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1404_11869.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1404_11869.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1404_11869.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1404_11869.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1404_11869.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1404_11869.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1404_11869.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1404_11869.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1404_11869.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1404_11869.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1404_11869.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1404_11869.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1404_11869.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1404_11869.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1404_11869.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___1404_11869.FStar_TypeChecker_Env.nbe)
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
                 let uu____11937 =
                   let uu____11939 =
                     let uu____11948 = drop_logic val_q  in
                     let uu____11951 = drop_logic q'  in
                     (uu____11948, uu____11951)  in
                   match uu____11939 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____11937
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____11978 =
                      let uu____11984 =
                        let uu____11986 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____11988 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____11990 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____11986 uu____11988 uu____11990
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____11984)
                       in
                    FStar_Errors.raise_error uu____11978 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____12027 =
                   let uu____12028 = FStar_Syntax_Subst.compress def  in
                   uu____12028.FStar_Syntax_Syntax.n  in
                 match uu____12027 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____12040,uu____12041) -> binders
                 | uu____12066 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____12078;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____12183) -> val_bs1
                     | (uu____12214,[]) -> val_bs1
                     | ((body_bv,uu____12246)::bt,(val_bv,aqual)::vt) ->
                         let uu____12303 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____12327) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___1473_12341 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___1475_12344 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___1475_12344.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___1473_12341.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1473_12341.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____12303
                      in
                   let uu____12351 =
                     let uu____12358 =
                       let uu____12359 =
                         let uu____12374 = rename_binders1 def_bs val_bs  in
                         (uu____12374, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____12359  in
                     FStar_Syntax_Syntax.mk uu____12358  in
                   uu____12351 FStar_Pervasives_Native.None r1
               | uu____12393 -> typ1  in
             let uu___1481_12394 = lb  in
             let uu____12395 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___1481_12394.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1481_12394.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____12395;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1481_12394.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___1481_12394.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1481_12394.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1481_12394.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____12398 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____12453  ->
                     fun lb  ->
                       match uu____12453 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____12499 =
                             let uu____12511 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____12511 with
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
                                   | uu____12591 ->
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
                                  (let uu____12638 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____12638, quals_opt1)))
                              in
                           (match uu____12499 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____12398 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____12742 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___2_12748  ->
                                match uu___2_12748 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____12753 -> false))
                         in
                      if uu____12742
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____12766 =
                    let uu____12773 =
                      let uu____12774 =
                        let uu____12788 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____12788)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____12774  in
                    FStar_Syntax_Syntax.mk uu____12773  in
                  uu____12766 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___1524_12807 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1524_12807.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1524_12807.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1524_12807.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1524_12807.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1524_12807.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1524_12807.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1524_12807.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1524_12807.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1524_12807.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1524_12807.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1524_12807.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1524_12807.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1524_12807.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1524_12807.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1524_12807.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1524_12807.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1524_12807.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1524_12807.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1524_12807.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1524_12807.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1524_12807.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1524_12807.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1524_12807.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1524_12807.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1524_12807.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1524_12807.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1524_12807.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1524_12807.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1524_12807.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1524_12807.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1524_12807.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1524_12807.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1524_12807.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1524_12807.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1524_12807.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1524_12807.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1524_12807.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1524_12807.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1524_12807.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1524_12807.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1524_12807.FStar_TypeChecker_Env.nbe)
                  }  in
                let e1 =
                  let uu____12810 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____12810
                  then
                    let drop_lbtyp e_lax =
                      let uu____12819 =
                        let uu____12820 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____12820.FStar_Syntax_Syntax.n  in
                      match uu____12819 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____12842 =
                              let uu____12843 = FStar_Syntax_Subst.compress e
                                 in
                              uu____12843.FStar_Syntax_Syntax.n  in
                            match uu____12842 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____12847,lb1::[]),uu____12849) ->
                                let uu____12865 =
                                  let uu____12866 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____12866.FStar_Syntax_Syntax.n  in
                                (match uu____12865 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____12871 -> false)
                            | uu____12873 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___1549_12877 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___1551_12892 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___1551_12892.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___1551_12892.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___1551_12892.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___1551_12892.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___1551_12892.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___1551_12892.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___1549_12877.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___1549_12877.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____12895 -> e_lax  in
                    let uu____12896 =
                      FStar_Util.record_time
                        (fun uu____12904  ->
                           let uu____12905 =
                             let uu____12906 =
                               let uu____12907 =
                                 FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                   (let uu___1555_12916 = env'  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___1555_12916.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___1555_12916.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___1555_12916.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___1555_12916.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___1555_12916.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___1555_12916.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___1555_12916.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___1555_12916.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___1555_12916.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___1555_12916.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___1555_12916.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___1555_12916.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___1555_12916.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___1555_12916.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___1555_12916.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___1555_12916.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___1555_12916.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___1555_12916.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___1555_12916.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___1555_12916.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___1555_12916.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___1555_12916.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___1555_12916.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___1555_12916.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___1555_12916.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___1555_12916.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___1555_12916.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___1555_12916.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___1555_12916.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___1555_12916.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___1555_12916.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___1555_12916.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___1555_12916.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___1555_12916.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___1555_12916.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___1555_12916.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___1555_12916.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___1555_12916.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___1555_12916.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___1555_12916.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___1555_12916.FStar_TypeChecker_Env.nbe)
                                    }) e
                                  in
                               FStar_All.pipe_right uu____12907
                                 (fun uu____12929  ->
                                    match uu____12929 with
                                    | (e1,uu____12937,uu____12938) -> e1)
                                in
                             FStar_All.pipe_right uu____12906
                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                  env')
                              in
                           FStar_All.pipe_right uu____12905 drop_lbtyp)
                       in
                    match uu____12896 with
                    | (e1,ms) ->
                        ((let uu____12944 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TwoPhases")
                             in
                          if uu____12944
                          then
                            let uu____12949 =
                              FStar_Syntax_Print.term_to_string e1  in
                            FStar_Util.print1
                              "Let binding after phase 1: %s\n" uu____12949
                          else ());
                         (let uu____12955 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TCDeclTime")
                             in
                          if uu____12955
                          then
                            let uu____12960 = FStar_Util.string_of_int ms  in
                            FStar_Util.print1
                              "Let binding elaborated (phase 1) in %s milliseconds\n"
                              uu____12960
                          else ());
                         e1)
                  else e  in
                let uu____12967 =
                  let uu____12976 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____12976 with
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
                (match uu____12967 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___1585_13081 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___1585_13081.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1585_13081.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1585_13081.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1585_13081.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___1592_13094 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1592_13094.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1592_13094.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___1592_13094.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___1592_13094.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1592_13094.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1592_13094.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____13095 =
                       FStar_Util.record_time
                         (fun uu____13114  ->
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              env' e1)
                        in
                     (match uu____13095 with
                      | (r1,ms) ->
                          ((let uu____13142 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TCDeclTime")
                               in
                            if uu____13142
                            then
                              let uu____13147 = FStar_Util.string_of_int ms
                                 in
                              FStar_Util.print1
                                "Let binding typechecked in phase 2 in %s milliseconds\n"
                                uu____13147
                            else ());
                           (let uu____13152 =
                              match r1 with
                              | ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                                   FStar_Syntax_Syntax.pos = uu____13177;
                                   FStar_Syntax_Syntax.vars = uu____13178;_},uu____13179,g)
                                  when FStar_TypeChecker_Env.is_trivial g ->
                                  let lbs2 =
                                    let uu____13209 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.snd lbs1)
                                        (FStar_List.map rename_parameters)
                                       in
                                    ((FStar_Pervasives_Native.fst lbs1),
                                      uu____13209)
                                     in
                                  let lbs3 =
                                    let uu____13233 =
                                      match post_tau with
                                      | FStar_Pervasives_Native.Some tau ->
                                          FStar_List.map (postprocess_lb tau)
                                            (FStar_Pervasives_Native.snd lbs2)
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.snd lbs2
                                       in
                                    ((FStar_Pervasives_Native.fst lbs2),
                                      uu____13233)
                                     in
                                  let quals1 =
                                    match e2.FStar_Syntax_Syntax.n with
                                    | FStar_Syntax_Syntax.Tm_meta
                                        (uu____13256,FStar_Syntax_Syntax.Meta_desugared
                                         (FStar_Syntax_Syntax.Masked_effect
                                         ))
                                        ->
                                        FStar_Syntax_Syntax.HasMaskedEffect
                                        :: quals
                                    | uu____13261 -> quals  in
                                  ((let uu___1622_13270 = se1  in
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_let
                                           (lbs3, lids));
                                      FStar_Syntax_Syntax.sigrng =
                                        (uu___1622_13270.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals = quals1;
                                      FStar_Syntax_Syntax.sigmeta =
                                        (uu___1622_13270.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (uu___1622_13270.FStar_Syntax_Syntax.sigattrs)
                                    }), lbs3)
                              | uu____13273 ->
                                  failwith
                                    "impossible (typechecking should preserve Tm_let)"
                               in
                            match uu____13152 with
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
                                 (let uu____13329 = log env1  in
                                  if uu____13329
                                  then
                                    let uu____13332 =
                                      let uu____13334 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.snd lbs1)
                                          (FStar_List.map
                                             (fun lb  ->
                                                let should_log =
                                                  let uu____13354 =
                                                    let uu____13363 =
                                                      let uu____13364 =
                                                        let uu____13367 =
                                                          FStar_Util.right
                                                            lb.FStar_Syntax_Syntax.lbname
                                                           in
                                                        uu____13367.FStar_Syntax_Syntax.fv_name
                                                         in
                                                      uu____13364.FStar_Syntax_Syntax.v
                                                       in
                                                    FStar_TypeChecker_Env.try_lookup_val_decl
                                                      env1 uu____13363
                                                     in
                                                  match uu____13354 with
                                                  | FStar_Pervasives_Native.None
                                                       -> true
                                                  | uu____13376 -> false  in
                                                if should_log
                                                then
                                                  let uu____13388 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  let uu____13390 =
                                                    FStar_Syntax_Print.term_to_string
                                                      lb.FStar_Syntax_Syntax.lbtyp
                                                     in
                                                  FStar_Util.format2
                                                    "let %s : %s" uu____13388
                                                    uu____13390
                                                else ""))
                                         in
                                      FStar_All.pipe_right uu____13334
                                        (FStar_String.concat "\n")
                                       in
                                    FStar_Util.print1 "%s\n" uu____13332
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
      (let uu____13442 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____13442
       then
         let uu____13445 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____13445
       else ());
      (let uu____13450 = get_fail_se se  in
       match uu____13450 with
       | FStar_Pervasives_Native.Some (uu____13471,false ) when
           let uu____13488 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____13488 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___1653_13514 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___1653_13514.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___1653_13514.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___1653_13514.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___1653_13514.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___1653_13514.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___1653_13514.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___1653_13514.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___1653_13514.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___1653_13514.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___1653_13514.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___1653_13514.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___1653_13514.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___1653_13514.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___1653_13514.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___1653_13514.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___1653_13514.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___1653_13514.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___1653_13514.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___1653_13514.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___1653_13514.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___1653_13514.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___1653_13514.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___1653_13514.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___1653_13514.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___1653_13514.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___1653_13514.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___1653_13514.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___1653_13514.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___1653_13514.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___1653_13514.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___1653_13514.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___1653_13514.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___1653_13514.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___1653_13514.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___1653_13514.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___1653_13514.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___1653_13514.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___1653_13514.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___1653_13514.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___1653_13514.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___1653_13514.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___1653_13514.FStar_TypeChecker_Env.nbe)
               }
             else env1  in
           ((let uu____13519 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____13519
             then
               let uu____13522 =
                 let uu____13524 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____13524
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____13522
             else ());
            (let uu____13538 =
               FStar_Errors.catch_errors
                 (fun uu____13568  ->
                    FStar_Options.with_saved_options
                      (fun uu____13580  -> tc_decl' env' se))
                in
             match uu____13538 with
             | (errs,uu____13592) ->
                 ((let uu____13622 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____13622
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____13657 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____13657  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____13669 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____13680 =
                            let uu____13690 = check_multi_eq errnos1 actual
                               in
                            match uu____13690 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- (Prims.parse_int "1")),
                                  (~- (Prims.parse_int "1")),
                                  (~- (Prims.parse_int "1")))
                             in
                          (match uu____13680 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____13755 =
                                   let uu____13761 =
                                     let uu____13763 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____13766 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____13769 =
                                       FStar_Util.string_of_int e  in
                                     let uu____13771 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____13773 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____13763 uu____13766 uu____13769
                                       uu____13771 uu____13773
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____13761)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____13755)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____13800 .
    'Auu____13800 ->
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
               (fun uu___3_13843  ->
                  match uu___3_13843 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____13846 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____13857) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____13865 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____13875 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____13880 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____13896 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____13922 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13948) ->
            let uu____13957 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13957
            then
              let for_export_bundle se1 uu____13994 =
                match uu____13994 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____14033,uu____14034) ->
                         let dec =
                           let uu___1729_14044 = se1  in
                           let uu____14045 =
                             let uu____14046 =
                               let uu____14053 =
                                 let uu____14054 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____14054  in
                               (l, us, uu____14053)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____14046
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____14045;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1729_14044.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1729_14044.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1729_14044.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____14064,uu____14065,uu____14066) ->
                         let dec =
                           let uu___1740_14074 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1740_14074.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1740_14074.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1740_14074.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____14079 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____14102,uu____14103,uu____14104) ->
            let uu____14105 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____14105 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____14129 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____14129
            then
              ([(let uu___1756_14148 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___1756_14148.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___1756_14148.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___1756_14148.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____14151 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_14157  ->
                         match uu___4_14157 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____14160 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____14166 ->
                             true
                         | uu____14168 -> false))
                  in
               if uu____14151 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____14189 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____14194 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____14199 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14204 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____14222) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____14236 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____14236
            then ([], hidden)
            else
              (let dec =
                 let uu____14257 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____14257;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____14268 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____14268
            then
              let uu____14279 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1791_14293 = se  in
                        let uu____14294 =
                          let uu____14295 =
                            let uu____14302 =
                              let uu____14303 =
                                let uu____14306 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____14306.FStar_Syntax_Syntax.fv_name  in
                              uu____14303.FStar_Syntax_Syntax.v  in
                            (uu____14302, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____14295  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____14294;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1791_14293.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1791_14293.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1791_14293.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____14279, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____14329 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____14329
       then
         let uu____14332 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____14332
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____14337 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____14355 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____14372) -> z3_reset_options env
       | FStar_Syntax_Syntax.Sig_pragma uu____14376 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____14386 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____14386) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____14387,uu____14388,uu____14389) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_14394  ->
                   match uu___5_14394 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____14397 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____14399,uu____14400) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_14409  ->
                   match uu___5_14409 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____14412 -> false))
           -> env
       | uu____14414 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____14483 se =
        match uu____14483 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____14536 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____14536
              then
                let uu____14539 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____14539
              else ());
             (let uu____14544 = tc_decl env1 se  in
              match uu____14544 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____14597 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____14597
                             then
                               let uu____14601 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____14601
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____14617 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____14617
                             then
                               let uu____14621 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____14621
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
                    (let uu____14638 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____14638
                     then
                       let uu____14643 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____14652 =
                                  let uu____14654 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____14654 "\n"  in
                                Prims.op_Hat s uu____14652) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____14643
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____14664 =
                       let uu____14673 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____14673
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____14715 se1 =
                            match uu____14715 with
                            | (exports1,hidden1) ->
                                let uu____14743 = for_export env3 hidden1 se1
                                   in
                                (match uu____14743 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____14664 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____14897 = acc  in
        match uu____14897 with
        | (uu____14932,uu____14933,env1,uu____14935) ->
            let uu____14948 =
              FStar_Util.record_time
                (fun uu____14995  -> process_one_decl acc se)
               in
            (match uu____14948 with
             | (r,ms_elapsed) ->
                 ((let uu____15061 =
                     ((FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TCDeclTime"))
                        ||
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.attr_eq
                              FStar_Syntax_Util.tcdecltime_attr)
                           se.FStar_Syntax_Syntax.sigattrs))
                       || (FStar_Options.timing ())
                      in
                   if uu____15061
                   then
                     let uu____15065 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____15067 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____15065 uu____15067
                   else ());
                  r))
         in
      let uu____15072 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____15072 with
      | (ses1,exports,env1,uu____15120) ->
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
          let uu___1893_15158 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1893_15158.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1893_15158.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1893_15158.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1893_15158.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1893_15158.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1893_15158.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1893_15158.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1893_15158.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1893_15158.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1893_15158.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___1893_15158.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1893_15158.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1893_15158.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1893_15158.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1893_15158.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___1893_15158.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1893_15158.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___1893_15158.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1893_15158.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___1893_15158.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1893_15158.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1893_15158.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1893_15158.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1893_15158.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1893_15158.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1893_15158.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1893_15158.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1893_15158.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1893_15158.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1893_15158.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1893_15158.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1893_15158.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1893_15158.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1893_15158.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___1893_15158.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___1893_15158.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1893_15158.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1893_15158.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1893_15158.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1893_15158.FStar_TypeChecker_Env.nbe)
          }  in
        let check_term lid univs1 t =
          let uu____15178 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____15178 with
          | (univs2,t1) ->
              ((let uu____15186 =
                  let uu____15188 =
                    let uu____15194 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____15194  in
                  FStar_All.pipe_left uu____15188
                    (FStar_Options.Other "Exports")
                   in
                if uu____15186
                then
                  let uu____15198 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____15200 =
                    let uu____15202 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____15202
                      (FStar_String.concat ", ")
                     in
                  let uu____15219 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____15198 uu____15200 uu____15219
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____15225 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____15225 (fun a1  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____15251 =
             let uu____15253 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____15255 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____15253 uu____15255
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____15251);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15266) ->
              let uu____15275 =
                let uu____15277 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15277  in
              if uu____15275
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____15291,uu____15292) ->
              let t =
                let uu____15304 =
                  let uu____15311 =
                    let uu____15312 =
                      let uu____15327 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____15327)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____15312  in
                  FStar_Syntax_Syntax.mk uu____15311  in
                uu____15304 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____15343,uu____15344,uu____15345) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____15355 =
                let uu____15357 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15357  in
              if uu____15355 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____15365,lbs),uu____15367) ->
              let uu____15378 =
                let uu____15380 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15380  in
              if uu____15378
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
              let uu____15403 =
                let uu____15405 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____15405  in
              if uu____15403
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____15426 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____15427 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____15434 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____15435 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____15436 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____15443 -> ()  in
        let uu____15444 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____15444 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____15550) -> true
             | uu____15552 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____15582 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____15621 ->
                   let uu____15622 =
                     let uu____15629 =
                       let uu____15630 =
                         let uu____15645 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____15645)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____15630  in
                     FStar_Syntax_Syntax.mk uu____15629  in
                   uu____15622 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____15662,uu____15663) ->
            let s1 =
              let uu___2017_15673 = s  in
              let uu____15674 =
                let uu____15675 =
                  let uu____15682 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____15682)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____15675  in
              let uu____15683 =
                let uu____15686 =
                  let uu____15689 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____15689  in
                FStar_Syntax_Syntax.Assumption :: uu____15686  in
              {
                FStar_Syntax_Syntax.sigel = uu____15674;
                FStar_Syntax_Syntax.sigrng =
                  (uu___2017_15673.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____15683;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2017_15673.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___2017_15673.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____15692 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____15717 lbdef =
        match uu____15717 with
        | (uvs,t) ->
            let attrs =
              let uu____15728 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____15728
              then
                let uu____15733 =
                  let uu____15734 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____15734
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____15733 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___2030_15737 = s  in
            let uu____15738 =
              let uu____15741 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____15741  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___2030_15737.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____15738;
              FStar_Syntax_Syntax.sigmeta =
                (uu___2030_15737.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____15759 -> failwith "Impossible!"  in
        let c_opt =
          let uu____15766 = FStar_Syntax_Util.is_unit t  in
          if uu____15766
          then
            let uu____15773 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____15773
          else
            (let uu____15780 =
               let uu____15781 = FStar_Syntax_Subst.compress t  in
               uu____15781.FStar_Syntax_Syntax.n  in
             match uu____15780 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____15788,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____15812 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____15824 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____15824
            then false
            else
              (let uu____15831 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____15831
               then true
               else
                 (let uu____15838 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____15838))
         in
      let extract_sigelt s =
        (let uu____15850 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____15850
         then
           let uu____15853 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____15853
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____15860 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____15880 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____15899 ->
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
                             (lid,uu____15945,uu____15946,uu____15947,uu____15948,uu____15949)
                             ->
                             ((let uu____15959 =
                                 let uu____15962 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____15962  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____15959);
                              (let uu____16011 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____16011 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____16015,uu____16016,uu____16017,uu____16018,uu____16019)
                             ->
                             ((let uu____16027 =
                                 let uu____16030 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____16030  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____16027);
                              sigelts1)
                         | uu____16079 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____16088 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____16088
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____16098 =
                    let uu___2094_16099 = s  in
                    let uu____16100 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2094_16099.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2094_16099.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____16100;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2094_16099.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2094_16099.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____16098])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____16111 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____16111
             then []
             else
               (let uu____16118 = lbs  in
                match uu____16118 with
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
                        (fun uu____16180  ->
                           match uu____16180 with
                           | (uu____16188,t,uu____16190) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____16207  ->
                             match uu____16207 with
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
                           (fun uu____16234  ->
                              match uu____16234 with
                              | (uu____16242,t,uu____16244) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____16256,uu____16257) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____16265 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____16294 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____16294) uu____16265
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____16298 =
                    let uu___2136_16299 = s  in
                    let uu____16300 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2136_16299.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2136_16299.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____16300;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2136_16299.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2136_16299.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____16298]
                else [])
             else
               (let uu____16307 =
                  let uu___2138_16308 = s  in
                  let uu____16309 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___2138_16308.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___2138_16308.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____16309;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___2138_16308.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___2138_16308.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____16307])
         | FStar_Syntax_Syntax.Sig_new_effect uu____16312 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____16313 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____16314 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____16327 -> [s])
         in
      let uu___2148_16328 = m  in
      let uu____16329 =
        let uu____16330 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____16330 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___2148_16328.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____16329;
        FStar_Syntax_Syntax.exports =
          (uu___2148_16328.FStar_Syntax_Syntax.exports);
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
        (fun uu____16381  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____16428  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____16443 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____16443
  
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
      (let uu____16532 = FStar_Options.debug_any ()  in
       if uu____16532
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
         let uu___2173_16548 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___2173_16548.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___2173_16548.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___2173_16548.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___2173_16548.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___2173_16548.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___2173_16548.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___2173_16548.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___2173_16548.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___2173_16548.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___2173_16548.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___2173_16548.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___2173_16548.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___2173_16548.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___2173_16548.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___2173_16548.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___2173_16548.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___2173_16548.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___2173_16548.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___2173_16548.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___2173_16548.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___2173_16548.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___2173_16548.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___2173_16548.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___2173_16548.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___2173_16548.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___2173_16548.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___2173_16548.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___2173_16548.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___2173_16548.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___2173_16548.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___2173_16548.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___2173_16548.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___2173_16548.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___2173_16548.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___2173_16548.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___2173_16548.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___2173_16548.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___2173_16548.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___2173_16548.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___2173_16548.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___2173_16548.FStar_TypeChecker_Env.nbe)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____16550 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____16550 with
       | (ses,exports,env3) ->
           ((let uu___2181_16583 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___2181_16583.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___2181_16583.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___2181_16583.FStar_Syntax_Syntax.is_interface)
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
        let uu____16612 = tc_decls env decls  in
        match uu____16612 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___2190_16643 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___2190_16643.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___2190_16643.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___2190_16643.FStar_Syntax_Syntax.is_interface)
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
        let uu____16704 = tc_partial_modul env01 m  in
        match uu____16704 with
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
                (let uu____16741 = FStar_Errors.get_err_count ()  in
                 uu____16741 = (Prims.parse_int "0"))
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____16752 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____16752
                then
                  let uu____16756 =
                    let uu____16758 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16758 then "" else " (in lax mode) "  in
                  let uu____16766 =
                    let uu____16768 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16768
                    then
                      let uu____16772 =
                        let uu____16774 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.op_Hat uu____16774 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____16772
                    else ""  in
                  let uu____16781 =
                    let uu____16783 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16783
                    then
                      let uu____16787 =
                        let uu____16789 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____16789 "\n"  in
                      Prims.op_Hat "\nto: " uu____16787
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____16756
                    uu____16766 uu____16781
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___2216_16803 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2216_16803.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2216_16803.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2216_16803.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2216_16803.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2216_16803.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2216_16803.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2216_16803.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2216_16803.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2216_16803.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2216_16803.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2216_16803.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2216_16803.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2216_16803.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2216_16803.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2216_16803.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2216_16803.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2216_16803.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2216_16803.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2216_16803.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2216_16803.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2216_16803.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2216_16803.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2216_16803.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2216_16803.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2216_16803.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2216_16803.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2216_16803.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2216_16803.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2216_16803.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2216_16803.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2216_16803.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___2216_16803.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2216_16803.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2216_16803.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2216_16803.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2216_16803.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2216_16803.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2216_16803.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2216_16803.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2216_16803.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2216_16803.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2216_16803.FStar_TypeChecker_Env.nbe)
                    }  in
                  let en02 =
                    let uu___2219_16805 = en01  in
                    let uu____16806 =
                      let uu____16821 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____16821, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2219_16805.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2219_16805.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2219_16805.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2219_16805.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2219_16805.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2219_16805.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2219_16805.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2219_16805.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2219_16805.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2219_16805.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2219_16805.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2219_16805.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2219_16805.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2219_16805.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2219_16805.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2219_16805.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2219_16805.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2219_16805.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2219_16805.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2219_16805.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2219_16805.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2219_16805.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2219_16805.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2219_16805.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2219_16805.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2219_16805.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2219_16805.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2219_16805.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2219_16805.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2219_16805.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2219_16805.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____16806;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2219_16805.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2219_16805.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2219_16805.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2219_16805.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2219_16805.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2219_16805.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2219_16805.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2219_16805.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2219_16805.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___2219_16805.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2219_16805.FStar_TypeChecker_Env.nbe)
                    }  in
                  let uu____16867 =
                    let uu____16869 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____16869  in
                  if uu____16867
                  then
                    ((let uu____16873 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____16873 (fun a2  -> ()));
                     z3_reset_options en02)
                  else en02  in
                let uu____16877 = tc_modul en0 modul_iface true  in
                match uu____16877 with
                | (modul_iface1,env) ->
                    ((let uu___2228_16890 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___2228_16890.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___2228_16890.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___2228_16890.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___2230_16894 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___2230_16894.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___2230_16894.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___2230_16894.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____16897 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____16897 FStar_Util.smap_clear);
               (let uu____16933 =
                  ((let uu____16937 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____16937) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____16940 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____16940)
                   in
                if uu____16933 then check_exports env modul exports else ());
               (let uu____16946 =
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____16946 (fun a3  -> ()));
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
        let uu____16961 =
          let uu____16963 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____16963  in
        push_context env uu____16961  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____16984 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____16995 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____16995 with | (uu____17002,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____17027 = FStar_Options.debug_any ()  in
         if uu____17027
         then
           let uu____17030 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____17030
         else ());
        (let uu____17042 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____17042
         then
           let uu____17045 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____17045
         else ());
        (let env1 =
           let uu___2260_17051 = env  in
           let uu____17052 =
             let uu____17054 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____17054  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___2260_17051.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___2260_17051.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___2260_17051.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___2260_17051.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___2260_17051.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___2260_17051.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___2260_17051.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___2260_17051.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___2260_17051.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___2260_17051.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___2260_17051.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___2260_17051.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___2260_17051.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___2260_17051.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___2260_17051.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___2260_17051.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___2260_17051.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___2260_17051.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___2260_17051.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___2260_17051.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____17052;
             FStar_TypeChecker_Env.lax_universes =
               (uu___2260_17051.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___2260_17051.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___2260_17051.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___2260_17051.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___2260_17051.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___2260_17051.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___2260_17051.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___2260_17051.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___2260_17051.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___2260_17051.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___2260_17051.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___2260_17051.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___2260_17051.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___2260_17051.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___2260_17051.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___2260_17051.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___2260_17051.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___2260_17051.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___2260_17051.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___2260_17051.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___2260_17051.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___2260_17051.FStar_TypeChecker_Env.nbe)
           }  in
         let uu____17056 = tc_modul env1 m b  in
         match uu____17056 with
         | (m1,env2) ->
             ((let uu____17068 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____17068
               then
                 let uu____17071 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____17071
               else ());
              (let uu____17077 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____17077
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
                         let uu____17115 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____17115 with
                         | (univnames1,e) ->
                             let uu___2282_17122 = lb  in
                             let uu____17123 =
                               let uu____17126 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____17126 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2282_17122.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2282_17122.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___2282_17122.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2282_17122.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____17123;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2282_17122.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2282_17122.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___2284_17127 = se  in
                       let uu____17128 =
                         let uu____17129 =
                           let uu____17136 =
                             let uu____17137 = FStar_List.map update lbs  in
                             (b1, uu____17137)  in
                           (uu____17136, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____17129  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____17128;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___2284_17127.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___2284_17127.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___2284_17127.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___2284_17127.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____17145 -> se  in
                 let normalized_module =
                   let uu___2288_17147 = m1  in
                   let uu____17148 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___2288_17147.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____17148;
                     FStar_Syntax_Syntax.exports =
                       (uu___2288_17147.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___2288_17147.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____17149 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____17149
               else ());
              (m1, env2)))
  