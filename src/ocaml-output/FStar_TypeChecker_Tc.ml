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
      if (FStar_List.length ed.FStar_Syntax_Syntax.binders) <> Prims.int_zero
      then
        (let uu____461 =
           let uu____467 =
             let uu____469 =
               FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname  in
             Prims.op_Hat
               "Effect parameters are not yet supported for layered effects: "
               uu____469
              in
           (FStar_Errors.Error_TypeError, uu____467)  in
         FStar_Errors.raise_err uu____461)
      else ();
      (let uu____475 =
         FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs  in
       match uu____475 with
       | (univs_opening,annotated_univ_names) ->
           let env_uvs =
             FStar_TypeChecker_Env.push_univ_vars env0 annotated_univ_names
              in
           let signature0 = ed.FStar_Syntax_Syntax.signature  in
           let uu____496 =
             let uu____501 =
               FStar_Syntax_Subst.subst univs_opening
                 ed.FStar_Syntax_Syntax.signature
                in
             FStar_TypeChecker_TcTerm.tc_trivial_guard env_uvs uu____501  in
           (match uu____496 with
            | (signature,uu____503) ->
                let ed1 =
                  let uu___86_505 = ed  in
                  {
                    FStar_Syntax_Syntax.is_layered =
                      (uu___86_505.FStar_Syntax_Syntax.is_layered);
                    FStar_Syntax_Syntax.cattributes =
                      (uu___86_505.FStar_Syntax_Syntax.cattributes);
                    FStar_Syntax_Syntax.mname =
                      (uu___86_505.FStar_Syntax_Syntax.mname);
                    FStar_Syntax_Syntax.univs =
                      (uu___86_505.FStar_Syntax_Syntax.univs);
                    FStar_Syntax_Syntax.binders =
                      (uu___86_505.FStar_Syntax_Syntax.binders);
                    FStar_Syntax_Syntax.signature = signature;
                    FStar_Syntax_Syntax.ret_wp =
                      (uu___86_505.FStar_Syntax_Syntax.ret_wp);
                    FStar_Syntax_Syntax.bind_wp =
                      (uu___86_505.FStar_Syntax_Syntax.bind_wp);
                    FStar_Syntax_Syntax.stronger =
                      (uu___86_505.FStar_Syntax_Syntax.stronger);
                    FStar_Syntax_Syntax.match_wps =
                      (uu___86_505.FStar_Syntax_Syntax.match_wps);
                    FStar_Syntax_Syntax.trivial =
                      (uu___86_505.FStar_Syntax_Syntax.trivial);
                    FStar_Syntax_Syntax.repr =
                      (uu___86_505.FStar_Syntax_Syntax.repr);
                    FStar_Syntax_Syntax.return_repr =
                      (uu___86_505.FStar_Syntax_Syntax.return_repr);
                    FStar_Syntax_Syntax.bind_repr =
                      (uu___86_505.FStar_Syntax_Syntax.bind_repr);
                    FStar_Syntax_Syntax.stronger_repr =
                      (uu___86_505.FStar_Syntax_Syntax.stronger_repr);
                    FStar_Syntax_Syntax.actions =
                      (uu___86_505.FStar_Syntax_Syntax.actions);
                    FStar_Syntax_Syntax.eff_attrs =
                      (uu___86_505.FStar_Syntax_Syntax.eff_attrs)
                  }  in
                let env =
                  let uu____507 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      ed1.FStar_Syntax_Syntax.signature
                     in
                  FStar_TypeChecker_Env.push_bv env_uvs uu____507  in
                let ed2 =
                  match annotated_univ_names with
                  | [] -> ed1
                  | uu____509 ->
                      let op uu____529 =
                        match uu____529 with
                        | (us,t) ->
                            let uu____548 =
                              let uu____549 =
                                FStar_Syntax_Subst.shift_subst
                                  (FStar_List.length us) univs_opening
                                 in
                              FStar_Syntax_Subst.subst uu____549 t  in
                            (us, uu____548)
                         in
                      let uu___96_554 = ed1  in
                      let uu____555 =
                        FStar_Syntax_Util.map_match_wps op
                          ed1.FStar_Syntax_Syntax.match_wps
                         in
                      let uu____560 =
                        let uu____561 =
                          op ([], (ed1.FStar_Syntax_Syntax.repr))  in
                        FStar_Pervasives_Native.snd uu____561  in
                      let uu____572 = op ed1.FStar_Syntax_Syntax.return_repr
                         in
                      let uu____573 = op ed1.FStar_Syntax_Syntax.bind_repr
                         in
                      let uu____574 =
                        FStar_Util.map_opt
                          ed1.FStar_Syntax_Syntax.stronger_repr op
                         in
                      {
                        FStar_Syntax_Syntax.is_layered =
                          (uu___96_554.FStar_Syntax_Syntax.is_layered);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___96_554.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___96_554.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs = annotated_univ_names;
                        FStar_Syntax_Syntax.binders =
                          (uu___96_554.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___96_554.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___96_554.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___96_554.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___96_554.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.match_wps = uu____555;
                        FStar_Syntax_Syntax.trivial =
                          (uu___96_554.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr = uu____560;
                        FStar_Syntax_Syntax.return_repr = uu____572;
                        FStar_Syntax_Syntax.bind_repr = uu____573;
                        FStar_Syntax_Syntax.stronger_repr = uu____574;
                        FStar_Syntax_Syntax.actions =
                          (uu___96_554.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___96_554.FStar_Syntax_Syntax.eff_attrs)
                      }
                   in
                let get_binders_from_signature signature1 =
                  let fail1 uu____604 =
                    let uu____605 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env ed2.FStar_Syntax_Syntax.mname signature1
                       in
                    let uu____611 =
                      FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname
                       in
                    FStar_Errors.raise_error uu____605 uu____611  in
                  let uu____620 =
                    let uu____621 = FStar_Syntax_Subst.compress signature1
                       in
                    uu____621.FStar_Syntax_Syntax.n  in
                  match uu____620 with
                  | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                      (match bs with
                       | (a,uu____663)::indices when
                           (FStar_List.length indices) >= Prims.int_one ->
                           let uu____690 =
                             let uu____691 =
                               FStar_Syntax_Subst.compress
                                 a.FStar_Syntax_Syntax.sort
                                in
                             uu____691.FStar_Syntax_Syntax.n  in
                           (match uu____690 with
                            | FStar_Syntax_Syntax.Tm_type uu____702 -> bs
                            | uu____703 -> fail1 ())
                       | uu____704 -> fail1 ())
                  | uu____713 -> fail1 ()  in
                let bs =
                  get_binders_from_signature
                    ed2.FStar_Syntax_Syntax.signature
                   in
                let check_and_gen1 env1 uu____753 k =
                  match uu____753 with
                  | (us,t) ->
                      (match annotated_univ_names with
                       | [] -> check_and_gen env1 t k
                       | uu____789 ->
                           let uu____792 =
                             FStar_Syntax_Subst.subst_tscheme univs_opening
                               (us, t)
                              in
                           (match uu____792 with
                            | (us1,t1) ->
                                let uu____815 =
                                  FStar_Syntax_Subst.open_univ_vars us1 t1
                                   in
                                (match uu____815 with
                                 | (us2,t2) ->
                                     let t3 =
                                       let uu____831 =
                                         FStar_TypeChecker_Env.push_univ_vars
                                           env1 us2
                                          in
                                       tc_check_trivial_guard uu____831 t2 k
                                        in
                                     let uu____832 =
                                       FStar_Syntax_Subst.close_univ_vars us2
                                         t3
                                        in
                                     (us2, uu____832))))
                   in
                let repr0 = ed2.FStar_Syntax_Syntax.repr  in
                let tc_repr repr bs1 =
                  let expected_repr_type =
                    let uu____870 = FStar_Syntax_Util.type_u ()  in
                    match uu____870 with
                    | (t,u) ->
                        let uu____879 =
                          FStar_Syntax_Syntax.mk_Total' t
                            (FStar_Pervasives_Native.Some u)
                           in
                        FStar_Syntax_Util.arrow bs1 uu____879
                     in
                  let repr1 =
                    tc_check_trivial_guard env repr expected_repr_type  in
                  (let uu____884 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "LayeredEffects")
                      in
                   if uu____884
                   then
                     let uu____889 = FStar_Syntax_Print.term_to_string repr1
                        in
                     let uu____891 =
                       FStar_Syntax_Print.term_to_string expected_repr_type
                        in
                     FStar_Util.print2
                       "Checked repr: %s against expected repr type: %s\n"
                       uu____889 uu____891
                   else ());
                  repr1  in
                let repr = tc_repr ed2.FStar_Syntax_Syntax.repr bs  in
                let uu____897 =
                  let bs1 = FStar_Syntax_Subst.open_binders bs  in
                  let uu____903 =
                    let uu____922 = FStar_List.hd bs1  in
                    let uu____935 = FStar_List.tl bs1  in
                    (uu____922, uu____935)  in
                  match uu____903 with
                  | (a,bs_indices) ->
                      let r =
                        FStar_Ident.range_of_lid
                          ed2.FStar_Syntax_Syntax.mname
                         in
                      let bs2 =
                        let uu____1008 =
                          let uu____1017 =
                            let uu____1024 =
                              let uu____1025 =
                                FStar_All.pipe_right a
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_All.pipe_right uu____1025
                                FStar_Syntax_Syntax.bv_to_name
                               in
                            FStar_Syntax_Syntax.null_binder uu____1024  in
                          [uu____1017]  in
                        a :: uu____1008  in
                      let uu____1052 =
                        let env1 = FStar_TypeChecker_Env.push_binders env bs2
                           in
                        FStar_List.fold_left
                          (fun uu____1096  ->
                             fun uu____1097  ->
                               match (uu____1096, uu____1097) with
                               | ((uvars1,gs,bs_substs),(b,uu____1150)) ->
                                   let uu____1185 =
                                     let uu____1198 =
                                       FStar_Syntax_Subst.subst bs_substs
                                         b.FStar_Syntax_Syntax.sort
                                        in
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "" r env1 uu____1198
                                      in
                                   (match uu____1185 with
                                    | (t,uu____1213,g) ->
                                        let uu____1227 =
                                          let uu____1230 =
                                            let uu____1233 =
                                              FStar_All.pipe_right t
                                                FStar_Syntax_Syntax.as_arg
                                               in
                                            [uu____1233]  in
                                          FStar_List.append uvars1 uu____1230
                                           in
                                        (uu____1227,
                                          (FStar_List.append gs [g]),
                                          (FStar_List.append bs_substs
                                             [FStar_Syntax_Syntax.NT (b, t)]))))
                          ([], [], []) bs_indices
                         in
                      (match uu____1052 with
                       | (uvars1,gs,uu____1254) ->
                           let expected_return_repr_type =
                             let repr_args =
                               let uu____1273 =
                                 FStar_Syntax_Util.arg_of_non_null_binder a
                                  in
                               uu____1273 :: uvars1  in
                             let repr_comp =
                               let uu____1277 =
                                 FStar_Syntax_Syntax.mk_Tm_app repr repr_args
                                   FStar_Pervasives_Native.None r
                                  in
                               FStar_Syntax_Syntax.mk_Total uu____1277  in
                             let repr_comp1 =
                               FStar_Syntax_Subst.close_comp bs2 repr_comp
                                in
                             let bs3 = FStar_Syntax_Subst.close_binders bs2
                                in
                             FStar_Syntax_Util.arrow bs3 repr_comp1  in
                           ((let uu____1281 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "LayeredEffects")
                                in
                             if uu____1281
                             then
                               let uu____1286 =
                                 FStar_Syntax_Print.tscheme_to_string
                                   ed2.FStar_Syntax_Syntax.return_repr
                                  in
                               let uu____1288 =
                                 FStar_Syntax_Print.term_to_string
                                   expected_return_repr_type
                                  in
                               FStar_Util.print2
                                 "Checking return_repr: %s against expected return_repr type: %s\n"
                                 uu____1286 uu____1288
                             else ());
                            (let return_repr =
                               check_and_gen1
                                 (let uu___174_1304 = env  in
                                  {
                                    FStar_TypeChecker_Env.solver =
                                      (uu___174_1304.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (uu___174_1304.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (uu___174_1304.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      (uu___174_1304.FStar_TypeChecker_Env.gamma);
                                    FStar_TypeChecker_Env.gamma_sig =
                                      (uu___174_1304.FStar_TypeChecker_Env.gamma_sig);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (uu___174_1304.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (uu___174_1304.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (uu___174_1304.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (uu___174_1304.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.attrtab =
                                      (uu___174_1304.FStar_TypeChecker_Env.attrtab);
                                    FStar_TypeChecker_Env.is_pattern =
                                      (uu___174_1304.FStar_TypeChecker_Env.is_pattern);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (uu___174_1304.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (uu___174_1304.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (uu___174_1304.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (uu___174_1304.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (uu___174_1304.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (uu___174_1304.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq = true;
                                    FStar_TypeChecker_Env.is_iface =
                                      (uu___174_1304.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (uu___174_1304.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax =
                                      (uu___174_1304.FStar_TypeChecker_Env.lax);
                                    FStar_TypeChecker_Env.lax_universes =
                                      (uu___174_1304.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.phase1 =
                                      (uu___174_1304.FStar_TypeChecker_Env.phase1);
                                    FStar_TypeChecker_Env.failhard =
                                      (uu___174_1304.FStar_TypeChecker_Env.failhard);
                                    FStar_TypeChecker_Env.nosynth =
                                      (uu___174_1304.FStar_TypeChecker_Env.nosynth);
                                    FStar_TypeChecker_Env.uvar_subtyping =
                                      (uu___174_1304.FStar_TypeChecker_Env.uvar_subtyping);
                                    FStar_TypeChecker_Env.tc_term =
                                      (uu___174_1304.FStar_TypeChecker_Env.tc_term);
                                    FStar_TypeChecker_Env.type_of =
                                      (uu___174_1304.FStar_TypeChecker_Env.type_of);
                                    FStar_TypeChecker_Env.universe_of =
                                      (uu___174_1304.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.check_type_of =
                                      (uu___174_1304.FStar_TypeChecker_Env.check_type_of);
                                    FStar_TypeChecker_Env.use_bv_sorts =
                                      (uu___174_1304.FStar_TypeChecker_Env.use_bv_sorts);
                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (uu___174_1304.FStar_TypeChecker_Env.qtbl_name_and_index);
                                    FStar_TypeChecker_Env.normalized_eff_names
                                      =
                                      (uu___174_1304.FStar_TypeChecker_Env.normalized_eff_names);
                                    FStar_TypeChecker_Env.fv_delta_depths =
                                      (uu___174_1304.FStar_TypeChecker_Env.fv_delta_depths);
                                    FStar_TypeChecker_Env.proof_ns =
                                      (uu___174_1304.FStar_TypeChecker_Env.proof_ns);
                                    FStar_TypeChecker_Env.synth_hook =
                                      (uu___174_1304.FStar_TypeChecker_Env.synth_hook);
                                    FStar_TypeChecker_Env.splice =
                                      (uu___174_1304.FStar_TypeChecker_Env.splice);
                                    FStar_TypeChecker_Env.postprocess =
                                      (uu___174_1304.FStar_TypeChecker_Env.postprocess);
                                    FStar_TypeChecker_Env.is_native_tactic =
                                      (uu___174_1304.FStar_TypeChecker_Env.is_native_tactic);
                                    FStar_TypeChecker_Env.identifier_info =
                                      (uu___174_1304.FStar_TypeChecker_Env.identifier_info);
                                    FStar_TypeChecker_Env.tc_hooks =
                                      (uu___174_1304.FStar_TypeChecker_Env.tc_hooks);
                                    FStar_TypeChecker_Env.dsenv =
                                      (uu___174_1304.FStar_TypeChecker_Env.dsenv);
                                    FStar_TypeChecker_Env.nbe =
                                      (uu___174_1304.FStar_TypeChecker_Env.nbe);
                                    FStar_TypeChecker_Env.strict_args_tab =
                                      (uu___174_1304.FStar_TypeChecker_Env.strict_args_tab)
                                  }) ed2.FStar_Syntax_Syntax.return_repr
                                 expected_return_repr_type
                                in
                             FStar_List.iter
                               (FStar_TypeChecker_Rel.force_trivial_guard env)
                               gs;
                             (let uu____1308 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "LayeredEffects")
                                 in
                              if uu____1308
                              then
                                let uu____1313 =
                                  FStar_Syntax_Print.tscheme_to_string
                                    return_repr
                                   in
                                let uu____1315 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_return_repr_type
                                   in
                                FStar_Util.print2
                                  "Checked return_repr: %s against expected return_repr type: %s\n"
                                  uu____1313 uu____1315
                              else ());
                             (let indices =
                                let uu____1323 =
                                  FStar_All.pipe_right uvars1
                                    (FStar_List.map
                                       FStar_Pervasives_Native.fst)
                                   in
                                FStar_All.pipe_right uu____1323
                                  (FStar_List.map FStar_Syntax_Subst.compress)
                                 in
                              let embedded_indices =
                                let uu____1357 =
                                  let uu____1364 =
                                    FStar_Syntax_Embeddings.e_list
                                      FStar_Syntax_Embeddings.e_any
                                     in
                                  FStar_Syntax_Embeddings.embed uu____1364
                                    indices
                                   in
                                uu____1357 FStar_Range.dummyRange
                                  FStar_Pervasives_Native.None
                                  FStar_Syntax_Embeddings.id_norm_cb
                                 in
                              let return_wp =
                                let uu____1374 =
                                  let uu____1375 =
                                    FStar_Syntax_Subst.close_binders bs2  in
                                  let uu____1376 =
                                    FStar_Syntax_Subst.close bs2
                                      embedded_indices
                                     in
                                  FStar_Syntax_Util.abs uu____1375 uu____1376
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_All.pipe_right uu____1374
                                  (FStar_TypeChecker_Util.generalize_universes
                                     env)
                                 in
                              (let uu____1380 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____1380
                               then
                                 let uu____1385 =
                                   FStar_Syntax_Print.tscheme_to_string
                                     return_wp
                                    in
                                 FStar_Util.print1 "return_wp: %s\n"
                                   uu____1385
                               else ());
                              (return_repr, return_wp)))))
                   in
                (match uu____897 with
                 | (return_repr,return_wp) ->
                     let uu____1392 =
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       let uu____1398 =
                         let uu____1417 = FStar_List.hd bs1  in
                         let uu____1430 = FStar_List.tl bs1  in
                         (uu____1417, uu____1430)  in
                       match uu____1398 with
                       | (a,bs_indices) ->
                           let r =
                             FStar_Ident.range_of_lid
                               ed2.FStar_Syntax_Syntax.mname
                              in
                           let uu____1494 =
                             match annotated_univ_names with
                             | [] ->
                                 let uu____1503 =
                                   FStar_TypeChecker_TcTerm.tc_trivial_guard
                                     env signature0
                                    in
                                 (match uu____1503 with
                                  | (signature1,uu____1513) ->
                                      let b_bs =
                                        get_binders_from_signature signature1
                                         in
                                      let repr1 = tc_repr repr0 b_bs  in
                                      (b_bs, repr1))
                             | uu____1524 ->
                                 let uu____1527 =
                                   let uu____1532 =
                                     let uu____1533 =
                                       FStar_Syntax_Subst.close_univ_vars
                                         annotated_univ_names
                                         ed2.FStar_Syntax_Syntax.signature
                                        in
                                     (annotated_univ_names, uu____1533)  in
                                   FStar_TypeChecker_Env.inst_tscheme
                                     uu____1532
                                    in
                                 (match uu____1527 with
                                  | (uu____1544,signature1) ->
                                      let new_univs =
                                        FStar_All.pipe_right
                                          annotated_univ_names
                                          (FStar_List.map
                                             (fun uu____1550  ->
                                                FStar_TypeChecker_Env.new_u_univ
                                                  ()))
                                         in
                                      let u_subst =
                                        FStar_TypeChecker_Env.mk_univ_subst
                                          annotated_univ_names new_univs
                                         in
                                      let uu____1554 =
                                        get_binders_from_signature signature1
                                         in
                                      let uu____1555 =
                                        let uu____1556 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names repr
                                           in
                                        FStar_Syntax_Subst.subst u_subst
                                          uu____1556
                                         in
                                      (uu____1554, uu____1555))
                              in
                           (match uu____1494 with
                            | (b_bs,b_repr) ->
                                let b_bs1 =
                                  FStar_Syntax_Subst.open_binders b_bs  in
                                let uu____1564 =
                                  let uu____1583 = FStar_List.hd b_bs1  in
                                  let uu____1596 = FStar_List.tl b_bs1  in
                                  (uu____1583, uu____1596)  in
                                (match uu____1564 with
                                 | (b,b_bs_indices) ->
                                     let b_bs_indices_arrow =
                                       FStar_All.pipe_right b_bs_indices
                                         (FStar_List.map
                                            (fun uu____1700  ->
                                               match uu____1700 with
                                               | (b1,q) ->
                                                   let uu____1719 =
                                                     let uu___216_1720 = b1
                                                        in
                                                     let uu____1721 =
                                                       let uu____1724 =
                                                         let uu____1733 =
                                                           let uu____1740 =
                                                             let uu____1741 =
                                                               FStar_All.pipe_right
                                                                 a
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____1741
                                                               FStar_Syntax_Syntax.bv_to_name
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____1740
                                                            in
                                                         [uu____1733]  in
                                                       let uu____1762 =
                                                         FStar_Syntax_Syntax.mk_Total
                                                           b1.FStar_Syntax_Syntax.sort
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         uu____1724
                                                         uu____1762
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.ppname
                                                         =
                                                         (uu___216_1720.FStar_Syntax_Syntax.ppname);
                                                       FStar_Syntax_Syntax.index
                                                         =
                                                         (uu___216_1720.FStar_Syntax_Syntax.index);
                                                       FStar_Syntax_Syntax.sort
                                                         = uu____1721
                                                     }  in
                                                   (uu____1719, q)))
                                        in
                                     let f_b =
                                       let uu____1768 =
                                         let uu____1769 =
                                           let uu____1774 =
                                             let uu____1775 =
                                               let uu____1778 =
                                                 FStar_All.pipe_right (a ::
                                                   bs_indices)
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____1778
                                                 (FStar_List.map
                                                    FStar_Syntax_Syntax.bv_to_name)
                                                in
                                             FStar_All.pipe_right uu____1775
                                               (FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____1774
                                            in
                                         uu____1769
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                          in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____1768
                                        in
                                     let g_b =
                                       let b_arg =
                                         let uu____1821 =
                                           let uu____1822 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_All.pipe_right uu____1822
                                             FStar_Syntax_Syntax.bv_to_name
                                            in
                                         FStar_All.pipe_right uu____1821
                                           FStar_Syntax_Syntax.as_arg
                                          in
                                       let x =
                                         let uu____1840 =
                                           let uu____1841 =
                                             FStar_All.pipe_right a
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_All.pipe_right uu____1841
                                             FStar_Syntax_Syntax.bv_to_name
                                            in
                                         FStar_Syntax_Syntax.null_binder
                                           uu____1840
                                          in
                                       let b_indices_args =
                                         let uu____1861 =
                                           let uu____1864 =
                                             FStar_All.pipe_right
                                               b_bs_indices_arrow
                                               (FStar_List.map
                                                  FStar_Pervasives_Native.fst)
                                              in
                                           FStar_All.pipe_right uu____1864
                                             (FStar_List.map
                                                FStar_Syntax_Syntax.bv_to_name)
                                            in
                                         FStar_All.pipe_right uu____1861
                                           (FStar_List.map
                                              (fun t  ->
                                                 let uu____1904 =
                                                   let uu____1905 =
                                                     let uu____1910 =
                                                       let uu____1911 =
                                                         let uu____1920 =
                                                           let uu____1921 =
                                                             FStar_All.pipe_right
                                                               x
                                                               FStar_Pervasives_Native.fst
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____1921
                                                             FStar_Syntax_Syntax.bv_to_name
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____1920
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____1911]  in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       t uu____1910
                                                      in
                                                   uu____1905
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____1904
                                                   FStar_Syntax_Syntax.as_arg))
                                          in
                                       let repr_app =
                                         FStar_Syntax_Syntax.mk_Tm_app b_repr
                                           (b_arg :: b_indices_args)
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                          in
                                       let uu____1965 =
                                         let uu____1966 =
                                           FStar_Syntax_Syntax.mk_Total
                                             repr_app
                                            in
                                         FStar_Syntax_Util.arrow [x]
                                           uu____1966
                                          in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____1965
                                        in
                                     let bs2 = a :: b ::
                                       (FStar_List.append bs_indices
                                          (FStar_List.append
                                             b_bs_indices_arrow [f_b; g_b]))
                                        in
                                     let uu____2032 =
                                       let env1 =
                                         FStar_TypeChecker_Env.push_binders
                                           env bs2
                                          in
                                       FStar_List.fold_left
                                         (fun uu____2076  ->
                                            fun uu____2077  ->
                                              match (uu____2076, uu____2077)
                                              with
                                              | ((uvars1,gs,bs_substs),
                                                 (b1,uu____2130)) ->
                                                  let uu____2165 =
                                                    let uu____2178 =
                                                      FStar_Syntax_Subst.subst
                                                        bs_substs
                                                        b1.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      "" r env1 uu____2178
                                                     in
                                                  (match uu____2165 with
                                                   | (t,uu____2193,g) ->
                                                       let uu____2207 =
                                                         let uu____2210 =
                                                           let uu____2213 =
                                                             FStar_All.pipe_right
                                                               t
                                                               FStar_Syntax_Syntax.as_arg
                                                              in
                                                           [uu____2213]  in
                                                         FStar_List.append
                                                           uvars1 uu____2210
                                                          in
                                                       (uu____2207,
                                                         (FStar_List.append
                                                            gs [g]),
                                                         (FStar_List.append
                                                            bs_substs
                                                            [FStar_Syntax_Syntax.NT
                                                               (b1, t)]))))
                                         ([], [], []) b_bs_indices
                                        in
                                     (match uu____2032 with
                                      | (uvars1,gs,uu____2234) ->
                                          let expected_bind_repr_type =
                                            let repr_args =
                                              let uu____2253 =
                                                FStar_Syntax_Util.arg_of_non_null_binder
                                                  b
                                                 in
                                              uu____2253 :: uvars1  in
                                            let repr_comp =
                                              let uu____2257 =
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  b_repr repr_args
                                                  FStar_Pervasives_Native.None
                                                  r
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____2257
                                               in
                                            let repr_comp1 =
                                              FStar_Syntax_Subst.close_comp
                                                bs2 repr_comp
                                               in
                                            let bs3 =
                                              FStar_Syntax_Subst.close_binders
                                                bs2
                                               in
                                            FStar_Syntax_Util.arrow bs3
                                              repr_comp1
                                             in
                                          ((let uu____2261 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other
                                                   "LayeredEffects")
                                               in
                                            if uu____2261
                                            then
                                              let uu____2266 =
                                                FStar_Syntax_Print.tscheme_to_string
                                                  ed2.FStar_Syntax_Syntax.bind_repr
                                                 in
                                              let uu____2268 =
                                                FStar_Syntax_Print.term_to_string
                                                  expected_bind_repr_type
                                                 in
                                              FStar_Util.print2
                                                "Checking bind_repr: %s against expected bind_repr type: %s\n"
                                                uu____2266 uu____2268
                                            else ());
                                           (let bind_repr =
                                              check_and_gen1
                                                (let uu___250_2284 = env  in
                                                 {
                                                   FStar_TypeChecker_Env.solver
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.solver);
                                                   FStar_TypeChecker_Env.range
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.range);
                                                   FStar_TypeChecker_Env.curmodule
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.curmodule);
                                                   FStar_TypeChecker_Env.gamma
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.gamma);
                                                   FStar_TypeChecker_Env.gamma_sig
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.gamma_sig);
                                                   FStar_TypeChecker_Env.gamma_cache
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.gamma_cache);
                                                   FStar_TypeChecker_Env.modules
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.modules);
                                                   FStar_TypeChecker_Env.expected_typ
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.expected_typ);
                                                   FStar_TypeChecker_Env.sigtab
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.sigtab);
                                                   FStar_TypeChecker_Env.attrtab
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.attrtab);
                                                   FStar_TypeChecker_Env.is_pattern
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.is_pattern);
                                                   FStar_TypeChecker_Env.instantiate_imp
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.instantiate_imp);
                                                   FStar_TypeChecker_Env.effects
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.effects);
                                                   FStar_TypeChecker_Env.generalize
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.generalize);
                                                   FStar_TypeChecker_Env.letrecs
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.letrecs);
                                                   FStar_TypeChecker_Env.top_level
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.top_level);
                                                   FStar_TypeChecker_Env.check_uvars
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.check_uvars);
                                                   FStar_TypeChecker_Env.use_eq
                                                     = true;
                                                   FStar_TypeChecker_Env.is_iface
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.is_iface);
                                                   FStar_TypeChecker_Env.admit
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.admit);
                                                   FStar_TypeChecker_Env.lax
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.lax);
                                                   FStar_TypeChecker_Env.lax_universes
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.lax_universes);
                                                   FStar_TypeChecker_Env.phase1
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.phase1);
                                                   FStar_TypeChecker_Env.failhard
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.failhard);
                                                   FStar_TypeChecker_Env.nosynth
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.nosynth);
                                                   FStar_TypeChecker_Env.uvar_subtyping
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.uvar_subtyping);
                                                   FStar_TypeChecker_Env.tc_term
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.tc_term);
                                                   FStar_TypeChecker_Env.type_of
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.type_of);
                                                   FStar_TypeChecker_Env.universe_of
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.universe_of);
                                                   FStar_TypeChecker_Env.check_type_of
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.check_type_of);
                                                   FStar_TypeChecker_Env.use_bv_sorts
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.use_bv_sorts);
                                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                   FStar_TypeChecker_Env.normalized_eff_names
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.normalized_eff_names);
                                                   FStar_TypeChecker_Env.fv_delta_depths
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.fv_delta_depths);
                                                   FStar_TypeChecker_Env.proof_ns
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.proof_ns);
                                                   FStar_TypeChecker_Env.synth_hook
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.synth_hook);
                                                   FStar_TypeChecker_Env.splice
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.splice);
                                                   FStar_TypeChecker_Env.postprocess
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.postprocess);
                                                   FStar_TypeChecker_Env.is_native_tactic
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.is_native_tactic);
                                                   FStar_TypeChecker_Env.identifier_info
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.identifier_info);
                                                   FStar_TypeChecker_Env.tc_hooks
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.tc_hooks);
                                                   FStar_TypeChecker_Env.dsenv
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.dsenv);
                                                   FStar_TypeChecker_Env.nbe
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.nbe);
                                                   FStar_TypeChecker_Env.strict_args_tab
                                                     =
                                                     (uu___250_2284.FStar_TypeChecker_Env.strict_args_tab)
                                                 })
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_bind_repr_type
                                               in
                                            FStar_List.iter
                                              (FStar_TypeChecker_Rel.force_trivial_guard
                                                 env) gs;
                                            (let uu____2288 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____2288
                                             then
                                               let uu____2293 =
                                                 FStar_Syntax_Print.tscheme_to_string
                                                   bind_repr
                                                  in
                                               let uu____2295 =
                                                 FStar_Syntax_Print.term_to_string
                                                   expected_bind_repr_type
                                                  in
                                               FStar_Util.print2
                                                 "Checked bind_repr: %s against expected bind_repr type: %s\n"
                                                 uu____2293 uu____2295
                                             else ());
                                            (let bs3 = a :: b ::
                                               (FStar_List.append bs_indices
                                                  b_bs_indices_arrow)
                                                in
                                             let indices =
                                               let uu____2330 =
                                                 FStar_All.pipe_right uvars1
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2330
                                                 (FStar_List.map
                                                    FStar_Syntax_Subst.compress)
                                                in
                                             let embedded_indices =
                                               let uu____2364 =
                                                 let uu____2371 =
                                                   FStar_Syntax_Embeddings.e_list
                                                     FStar_Syntax_Embeddings.e_any
                                                    in
                                                 FStar_Syntax_Embeddings.embed
                                                   uu____2371 indices
                                                  in
                                               uu____2364
                                                 FStar_Range.dummyRange
                                                 FStar_Pervasives_Native.None
                                                 FStar_Syntax_Embeddings.id_norm_cb
                                                in
                                             let bind_wp =
                                               let uu____2381 =
                                                 let uu____2382 =
                                                   FStar_Syntax_Subst.close_binders
                                                     bs3
                                                    in
                                                 let uu____2383 =
                                                   FStar_Syntax_Subst.close
                                                     bs3 embedded_indices
                                                    in
                                                 FStar_Syntax_Util.abs
                                                   uu____2382 uu____2383
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2381
                                                 (FStar_TypeChecker_Util.generalize_universes
                                                    env)
                                                in
                                             (let uu____2387 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____2387
                                              then
                                                let uu____2392 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    bind_wp
                                                   in
                                                FStar_Util.print1
                                                  "bind_wp: %s\n" uu____2392
                                              else ());
                                             (bind_repr, bind_wp)))))))
                        in
                     (match uu____1392 with
                      | (bind_repr,bind_wp) ->
                          let uu____2399 =
                            let uu____2404 =
                              FStar_TypeChecker_Util.generalize_universes
                                env0 ed2.FStar_Syntax_Syntax.signature
                               in
                            match uu____2404 with
                            | (univs1,signature1) ->
                                (match annotated_univ_names with
                                 | [] -> (univs1, signature1)
                                 | uu____2423 ->
                                     let uu____2426 =
                                       ((FStar_List.length univs1) =
                                          (FStar_List.length
                                             annotated_univ_names))
                                         &&
                                         (FStar_List.forall2
                                            (fun u1  ->
                                               fun u2  ->
                                                 let uu____2433 =
                                                   FStar_Syntax_Syntax.order_univ_name
                                                     u1 u2
                                                    in
                                                 uu____2433 = Prims.int_zero)
                                            univs1 annotated_univ_names)
                                        in
                                     if uu____2426
                                     then (univs1, signature1)
                                     else
                                       (let uu____2444 =
                                          let uu____2450 =
                                            let uu____2452 =
                                              FStar_Util.string_of_int
                                                (FStar_List.length
                                                   annotated_univ_names)
                                               in
                                            let uu____2454 =
                                              FStar_Util.string_of_int
                                                (FStar_List.length univs1)
                                               in
                                            FStar_Util.format2
                                              "Expected an effect definition with %s universes; but found %s"
                                              uu____2452 uu____2454
                                             in
                                          (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                            uu____2450)
                                           in
                                        FStar_Errors.raise_error uu____2444
                                          (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                             in
                          (match uu____2399 with
                           | (univs1,signature1) ->
                               let close1 n1 ts =
                                 let ts1 =
                                   FStar_Syntax_Subst.close_univ_vars_tscheme
                                     univs1 ts
                                    in
                                 let m =
                                   FStar_List.length
                                     (FStar_Pervasives_Native.fst ts1)
                                    in
                                 (let uu____2484 =
                                    ((n1 >= Prims.int_zero) &&
                                       (let uu____2488 =
                                          FStar_Syntax_Util.is_unknown
                                            (FStar_Pervasives_Native.snd ts1)
                                           in
                                        Prims.op_Negation uu____2488))
                                      && (m <> n1)
                                     in
                                  if uu____2484
                                  then
                                    let error =
                                      if m < n1
                                      then "not universe-polymorphic enough"
                                      else "too universe-polymorphic"  in
                                    let err_msg =
                                      let uu____2506 =
                                        FStar_Util.string_of_int m  in
                                      let uu____2508 =
                                        FStar_Util.string_of_int n1  in
                                      let uu____2510 =
                                        FStar_Syntax_Print.tscheme_to_string
                                          ts1
                                         in
                                      FStar_Util.format4
                                        "The effect combinator is %s (m,n=%s,%s) (%s)"
                                        error uu____2506 uu____2508
                                        uu____2510
                                       in
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                        err_msg)
                                      (FStar_Pervasives_Native.snd ts1).FStar_Syntax_Syntax.pos
                                  else ());
                                 ts1  in
                               let ed3 =
                                 let uu___286_2521 = ed2  in
                                 let uu____2522 =
                                   close1 Prims.int_zero return_wp  in
                                 let uu____2524 =
                                   close1 Prims.int_one bind_wp  in
                                 let uu____2526 =
                                   close1 Prims.int_zero return_repr  in
                                 let uu____2528 =
                                   close1 Prims.int_one bind_repr  in
                                 {
                                   FStar_Syntax_Syntax.is_layered =
                                     (uu___286_2521.FStar_Syntax_Syntax.is_layered);
                                   FStar_Syntax_Syntax.cattributes =
                                     (uu___286_2521.FStar_Syntax_Syntax.cattributes);
                                   FStar_Syntax_Syntax.mname =
                                     (uu___286_2521.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.univs = univs1;
                                   FStar_Syntax_Syntax.binders = [];
                                   FStar_Syntax_Syntax.signature = signature1;
                                   FStar_Syntax_Syntax.ret_wp = uu____2522;
                                   FStar_Syntax_Syntax.bind_wp = uu____2524;
                                   FStar_Syntax_Syntax.stronger =
                                     (uu___286_2521.FStar_Syntax_Syntax.stronger);
                                   FStar_Syntax_Syntax.match_wps =
                                     (uu___286_2521.FStar_Syntax_Syntax.match_wps);
                                   FStar_Syntax_Syntax.trivial =
                                     (uu___286_2521.FStar_Syntax_Syntax.trivial);
                                   FStar_Syntax_Syntax.repr = repr;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____2526;
                                   FStar_Syntax_Syntax.bind_repr = uu____2528;
                                   FStar_Syntax_Syntax.stronger_repr =
                                     (uu___286_2521.FStar_Syntax_Syntax.stronger_repr);
                                   FStar_Syntax_Syntax.actions =
                                     (uu___286_2521.FStar_Syntax_Syntax.actions);
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (uu___286_2521.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               ((let uu____2537 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env0)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____2537
                                 then
                                   let uu____2542 =
                                     FStar_Syntax_Print.eff_decl_to_string
                                       false ed3
                                      in
                                   FStar_Util.print1
                                     "Typechecked layered effect: %s\n"
                                     uu____2542
                                 else ());
                                ed3))))))
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      let uu____2559 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs  in
      match uu____2559 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____2591 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst uu____2591 t  in
          let open_univs_binders n_binders bs =
            let uu____2607 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst_binders uu____2607 bs  in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders  in
          let uu____2617 =
            let uu____2624 =
              open_univs_binders Prims.int_zero
                ed.FStar_Syntax_Syntax.binders
               in
            let uu____2626 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature  in
            FStar_Syntax_Subst.open_term' uu____2624 uu____2626  in
          (match uu____2617 with
           | (effect_params_un,signature_un,opening) ->
               let env =
                 FStar_TypeChecker_Env.push_univ_vars env0
                   annotated_univ_names
                  in
               let uu____2631 =
                 FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un  in
               (match uu____2631 with
                | (effect_params,env1,uu____2640) ->
                    let uu____2641 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                        signature_un
                       in
                    (match uu____2641 with
                     | (signature,uu____2647) ->
                         let ed1 =
                           let uu___315_2649 = ed  in
                           {
                             FStar_Syntax_Syntax.is_layered =
                               (uu___315_2649.FStar_Syntax_Syntax.is_layered);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___315_2649.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___315_2649.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___315_2649.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___315_2649.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___315_2649.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___315_2649.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.match_wps =
                               (uu___315_2649.FStar_Syntax_Syntax.match_wps);
                             FStar_Syntax_Syntax.trivial =
                               (uu___315_2649.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___315_2649.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___315_2649.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___315_2649.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.stronger_repr =
                               (uu___315_2649.FStar_Syntax_Syntax.stronger_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___315_2649.FStar_Syntax_Syntax.actions);
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___315_2649.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____2677 ->
                               let op uu____2709 =
                                 match uu____2709 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us  in
                                     let uu____2729 =
                                       let uu____2730 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening
                                          in
                                       let uu____2733 = open_univs n_us t  in
                                       FStar_Syntax_Subst.subst uu____2730
                                         uu____2733
                                        in
                                     (us, uu____2729)
                                  in
                               let uu___327_2736 = ed1  in
                               let uu____2737 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp  in
                               let uu____2738 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp  in
                               let uu____2739 =
                                 op ed1.FStar_Syntax_Syntax.stronger  in
                               let uu____2740 =
                                 FStar_Syntax_Util.map_match_wps op
                                   ed1.FStar_Syntax_Syntax.match_wps
                                  in
                               let uu____2745 =
                                 FStar_Util.map_opt
                                   ed1.FStar_Syntax_Syntax.trivial op
                                  in
                               let uu____2748 =
                                 let uu____2749 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr))
                                    in
                                 FStar_Pervasives_Native.snd uu____2749  in
                               let uu____2760 =
                                 op ed1.FStar_Syntax_Syntax.return_repr  in
                               let uu____2761 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr  in
                               let uu____2762 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___330_2770 = a  in
                                      let uu____2771 =
                                        let uu____2772 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_defn))
                                           in
                                        FStar_Pervasives_Native.snd
                                          uu____2772
                                         in
                                      let uu____2783 =
                                        let uu____2784 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_typ))
                                           in
                                        FStar_Pervasives_Native.snd
                                          uu____2784
                                         in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___330_2770.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___330_2770.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___330_2770.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___330_2770.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____2771;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____2783
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.is_layered =
                                   (uu___327_2736.FStar_Syntax_Syntax.is_layered);
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___327_2736.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___327_2736.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___327_2736.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___327_2736.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____2737;
                                 FStar_Syntax_Syntax.bind_wp = uu____2738;
                                 FStar_Syntax_Syntax.stronger = uu____2739;
                                 FStar_Syntax_Syntax.match_wps = uu____2740;
                                 FStar_Syntax_Syntax.trivial = uu____2745;
                                 FStar_Syntax_Syntax.repr = uu____2748;
                                 FStar_Syntax_Syntax.return_repr = uu____2760;
                                 FStar_Syntax_Syntax.bind_repr = uu____2761;
                                 FStar_Syntax_Syntax.stronger_repr =
                                   (uu___327_2736.FStar_Syntax_Syntax.stronger_repr);
                                 FStar_Syntax_Syntax.actions = uu____2762;
                                 FStar_Syntax_Syntax.eff_attrs =
                                   (uu___327_2736.FStar_Syntax_Syntax.eff_attrs)
                               }
                            in
                         let wp_with_fresh_result_type env2 mname signature1
                           =
                           let fail1 t =
                             let uu____2829 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env2 mname t
                                in
                             let uu____2835 = FStar_Ident.range_of_lid mname
                                in
                             FStar_Errors.raise_error uu____2829 uu____2835
                              in
                           let uu____2842 =
                             let uu____2843 =
                               FStar_Syntax_Subst.compress signature1  in
                             uu____2843.FStar_Syntax_Syntax.n  in
                           match uu____2842 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs
                                  in
                               (match bs1 with
                                | (a,uu____2882)::(wp,uu____2884)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____2913 -> fail1 signature1)
                           | uu____2914 -> fail1 signature1  in
                         let uu____2915 =
                           wp_with_fresh_result_type env1
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature
                            in
                         (match uu____2915 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____2939 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____2946 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env1 signature_un
                                       in
                                    (match uu____2946 with
                                     | (signature1,uu____2958) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____2959 ->
                                    let uu____2962 =
                                      let uu____2967 =
                                        let uu____2968 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature
                                           in
                                        (annotated_univ_names, uu____2968)
                                         in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____2967
                                       in
                                    (match uu____2962 with
                                     | (uu____2981,signature1) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                 in
                              let env2 =
                                let uu____2984 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                   in
                                FStar_TypeChecker_Env.push_bv env1 uu____2984
                                 in
                              ((let uu____2986 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____2986
                                then
                                  let uu____2991 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname
                                     in
                                  let uu____2993 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders
                                     in
                                  let uu____2996 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature
                                     in
                                  let uu____2998 =
                                    let uu____3000 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    FStar_Syntax_Print.term_to_string
                                      uu____3000
                                     in
                                  let uu____3001 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort
                                     in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____2991 uu____2993 uu____2996
                                    uu____2998 uu____3001
                                else ());
                               (let check_and_gen' env3 uu____3036 k =
                                  match uu____3036 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env3 t k
                                       | uu____3072::uu____3073 ->
                                           let uu____3076 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t)
                                              in
                                           (match uu____3076 with
                                            | (us1,t1) ->
                                                let uu____3099 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1
                                                   in
                                                (match uu____3099 with
                                                 | (us2,t2) ->
                                                     let uu____3114 =
                                                       let uu____3115 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env3 us2
                                                          in
                                                       tc_check_trivial_guard
                                                         uu____3115 t2 k
                                                        in
                                                     let uu____3116 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2
                                                        in
                                                     (us2, uu____3116))))
                                   in
                                let return_wp =
                                  let expected_k =
                                    let uu____3135 =
                                      let uu____3144 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____3151 =
                                        let uu____3160 =
                                          let uu____3167 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____3167
                                           in
                                        [uu____3160]  in
                                      uu____3144 :: uu____3151  in
                                    let uu____3186 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                    FStar_Syntax_Util.arrow uu____3135
                                      uu____3186
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                   in
                                let bind_wp =
                                  let uu____3190 = fresh_effect_signature ()
                                     in
                                  match uu____3190 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____3206 =
                                          let uu____3215 =
                                            let uu____3222 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____3222
                                             in
                                          [uu____3215]  in
                                        let uu____3235 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____3206
                                          uu____3235
                                         in
                                      let expected_k =
                                        let uu____3241 =
                                          let uu____3250 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____3257 =
                                            let uu____3266 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____3273 =
                                              let uu____3282 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____3289 =
                                                let uu____3298 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____3305 =
                                                  let uu____3314 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b
                                                     in
                                                  [uu____3314]  in
                                                uu____3298 :: uu____3305  in
                                              uu____3282 :: uu____3289  in
                                            uu____3266 :: uu____3273  in
                                          uu____3250 :: uu____3257  in
                                        let uu____3357 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____3241
                                          uu____3357
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k
                                   in
                                let uu____3360 =
                                  FStar_Syntax_Util.get_match_with_close_wps
                                    ed2.FStar_Syntax_Syntax.match_wps
                                   in
                                match uu____3360 with
                                | (if_then_else1,ite_wp,close_wp) ->
                                    let if_then_else2 =
                                      let p =
                                        let uu____3380 =
                                          let uu____3383 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____3383
                                           in
                                        let uu____3384 =
                                          let uu____3385 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____3385
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____3380
                                          uu____3384
                                         in
                                      let expected_k =
                                        let uu____3397 =
                                          let uu____3406 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____3413 =
                                            let uu____3422 =
                                              FStar_Syntax_Syntax.mk_binder p
                                               in
                                            let uu____3429 =
                                              let uu____3438 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              let uu____3445 =
                                                let uu____3454 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____3454]  in
                                              uu____3438 :: uu____3445  in
                                            uu____3422 :: uu____3429  in
                                          uu____3406 :: uu____3413  in
                                        let uu____3491 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____3397
                                          uu____3491
                                         in
                                      check_and_gen' env2 if_then_else1
                                        expected_k
                                       in
                                    let ite_wp1 =
                                      let expected_k =
                                        let uu____3506 =
                                          let uu____3515 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____3522 =
                                            let uu____3531 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____3531]  in
                                          uu____3515 :: uu____3522  in
                                        let uu____3556 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____3506
                                          uu____3556
                                         in
                                      check_and_gen' env2 ite_wp expected_k
                                       in
                                    let close_wp1 =
                                      let b =
                                        let uu____3569 =
                                          let uu____3572 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____3572
                                           in
                                        let uu____3573 =
                                          let uu____3574 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____3574
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____3569
                                          uu____3573
                                         in
                                      let b_wp_a =
                                        let uu____3586 =
                                          let uu____3595 =
                                            let uu____3602 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                b
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____3602
                                             in
                                          [uu____3595]  in
                                        let uu____3615 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____3586
                                          uu____3615
                                         in
                                      let expected_k =
                                        let uu____3621 =
                                          let uu____3630 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____3637 =
                                            let uu____3646 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____3653 =
                                              let uu____3662 =
                                                FStar_Syntax_Syntax.null_binder
                                                  b_wp_a
                                                 in
                                              [uu____3662]  in
                                            uu____3646 :: uu____3653  in
                                          uu____3630 :: uu____3637  in
                                        let uu____3693 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____3621
                                          uu____3693
                                         in
                                      check_and_gen' env2 close_wp expected_k
                                       in
                                    let stronger =
                                      let uu____3697 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____3697 with
                                      | (t,uu____3703) ->
                                          let expected_k =
                                            let uu____3707 =
                                              let uu____3716 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____3723 =
                                                let uu____3732 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____3739 =
                                                  let uu____3748 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____3748]  in
                                                uu____3732 :: uu____3739  in
                                              uu____3716 :: uu____3723  in
                                            let uu____3779 =
                                              FStar_Syntax_Syntax.mk_Total t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____3707 uu____3779
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.stronger
                                            expected_k
                                       in
                                    let trivial_wp =
                                      match ed2.FStar_Syntax_Syntax.trivial
                                      with
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some trivial
                                          ->
                                          let uu____3788 =
                                            FStar_Syntax_Util.type_u ()  in
                                          (match uu____3788 with
                                           | (t,uu____3796) ->
                                               let expected_k =
                                                 let uu____3800 =
                                                   let uu____3809 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       a
                                                      in
                                                   let uu____3816 =
                                                     let uu____3825 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         wp_a
                                                        in
                                                     [uu____3825]  in
                                                   uu____3809 :: uu____3816
                                                    in
                                                 let uu____3850 =
                                                   FStar_Syntax_Syntax.mk_GTotal
                                                     t
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____3800 uu____3850
                                                  in
                                               let uu____3853 =
                                                 check_and_gen' env2 trivial
                                                   expected_k
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____3853)
                                       in
                                    let uu____3854 =
                                      let uu____3867 =
                                        let uu____3868 =
                                          FStar_Syntax_Subst.compress
                                            ed2.FStar_Syntax_Syntax.repr
                                           in
                                        uu____3868.FStar_Syntax_Syntax.n  in
                                      match uu____3867 with
                                      | FStar_Syntax_Syntax.Tm_unknown  ->
                                          ((ed2.FStar_Syntax_Syntax.repr),
                                            (ed2.FStar_Syntax_Syntax.bind_repr),
                                            (ed2.FStar_Syntax_Syntax.return_repr),
                                            (ed2.FStar_Syntax_Syntax.actions))
                                      | uu____3887 ->
                                          let repr =
                                            let uu____3889 =
                                              FStar_Syntax_Util.type_u ()  in
                                            match uu____3889 with
                                            | (t,uu____3895) ->
                                                let expected_k =
                                                  let uu____3899 =
                                                    let uu____3908 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        a
                                                       in
                                                    let uu____3915 =
                                                      let uu____3924 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          wp_a
                                                         in
                                                      [uu____3924]  in
                                                    uu____3908 :: uu____3915
                                                     in
                                                  let uu____3949 =
                                                    FStar_Syntax_Syntax.mk_GTotal
                                                      t
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____3899 uu____3949
                                                   in
                                                tc_check_trivial_guard env2
                                                  ed2.FStar_Syntax_Syntax.repr
                                                  expected_k
                                             in
                                          let mk_repr' t wp =
                                            let repr1 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Env.EraseUniverses;
                                                FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                env2 repr
                                               in
                                            let uu____3966 =
                                              let uu____3973 =
                                                let uu____3974 =
                                                  let uu____3991 =
                                                    let uu____4002 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        t
                                                       in
                                                    let uu____4011 =
                                                      let uu____4022 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          wp
                                                         in
                                                      [uu____4022]  in
                                                    uu____4002 :: uu____4011
                                                     in
                                                  (repr1, uu____3991)  in
                                                FStar_Syntax_Syntax.Tm_app
                                                  uu____3974
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____3973
                                               in
                                            uu____3966
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          let mk_repr a1 wp =
                                            let uu____4080 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            mk_repr' uu____4080 wp  in
                                          let destruct_repr t =
                                            let uu____4095 =
                                              let uu____4096 =
                                                FStar_Syntax_Subst.compress t
                                                 in
                                              uu____4096.FStar_Syntax_Syntax.n
                                               in
                                            match uu____4095 with
                                            | FStar_Syntax_Syntax.Tm_app
                                                (uu____4107,(t1,uu____4109)::
                                                 (wp,uu____4111)::[])
                                                -> (t1, wp)
                                            | uu____4170 ->
                                                failwith
                                                  "Unexpected repr type"
                                             in
                                          let bind_repr =
                                            let r =
                                              let uu____4182 =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  FStar_Parser_Const.range_0
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              FStar_All.pipe_right uu____4182
                                                FStar_Syntax_Syntax.fv_to_tm
                                               in
                                            let uu____4183 =
                                              fresh_effect_signature ()  in
                                            match uu____4183 with
                                            | (b,wp_b) ->
                                                let a_wp_b =
                                                  let uu____4199 =
                                                    let uu____4208 =
                                                      let uu____4215 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.null_binder
                                                        uu____4215
                                                       in
                                                    [uu____4208]  in
                                                  let uu____4228 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      wp_b
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____4199 uu____4228
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
                                                  let uu____4236 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "x_a"
                                                    FStar_Pervasives_Native.None
                                                    uu____4236
                                                   in
                                                let wp_g_x =
                                                  let uu____4241 =
                                                    let uu____4246 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        wp_g
                                                       in
                                                    let uu____4247 =
                                                      let uu____4248 =
                                                        let uu____4257 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Syntax.as_arg
                                                          uu____4257
                                                         in
                                                      [uu____4248]  in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____4246 uu____4247
                                                     in
                                                  uu____4241
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                let res =
                                                  let wp =
                                                    let uu____4288 =
                                                      let uu____4293 =
                                                        let uu____4294 =
                                                          FStar_TypeChecker_Env.inst_tscheme
                                                            bind_wp
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4294
                                                          FStar_Pervasives_Native.snd
                                                         in
                                                      let uu____4303 =
                                                        let uu____4304 =
                                                          let uu____4307 =
                                                            let uu____4310 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                a
                                                               in
                                                            let uu____4311 =
                                                              let uu____4314
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  b
                                                                 in
                                                              let uu____4315
                                                                =
                                                                let uu____4318
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f
                                                                   in
                                                                let uu____4319
                                                                  =
                                                                  let uu____4322
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                  [uu____4322]
                                                                   in
                                                                uu____4318 ::
                                                                  uu____4319
                                                                 in
                                                              uu____4314 ::
                                                                uu____4315
                                                               in
                                                            uu____4310 ::
                                                              uu____4311
                                                             in
                                                          r :: uu____4307  in
                                                        FStar_List.map
                                                          FStar_Syntax_Syntax.as_arg
                                                          uu____4304
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____4293 uu____4303
                                                       in
                                                    uu____4288
                                                      FStar_Pervasives_Native.None
                                                      FStar_Range.dummyRange
                                                     in
                                                  mk_repr b wp  in
                                                let maybe_range_arg =
                                                  let uu____4340 =
                                                    FStar_Util.for_some
                                                      (FStar_Syntax_Util.attr_eq
                                                         FStar_Syntax_Util.dm4f_bind_range_attr)
                                                      ed2.FStar_Syntax_Syntax.eff_attrs
                                                     in
                                                  if uu____4340
                                                  then
                                                    let uu____4351 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        FStar_Syntax_Syntax.t_range
                                                       in
                                                    let uu____4358 =
                                                      let uu____4367 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          FStar_Syntax_Syntax.t_range
                                                         in
                                                      [uu____4367]  in
                                                    uu____4351 :: uu____4358
                                                  else []  in
                                                let expected_k =
                                                  let uu____4403 =
                                                    let uu____4412 =
                                                      let uu____4421 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a
                                                         in
                                                      let uu____4428 =
                                                        let uu____4437 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            b
                                                           in
                                                        [uu____4437]  in
                                                      uu____4421 ::
                                                        uu____4428
                                                       in
                                                    let uu____4462 =
                                                      let uu____4471 =
                                                        let uu____4480 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_f
                                                           in
                                                        let uu____4487 =
                                                          let uu____4496 =
                                                            let uu____4503 =
                                                              let uu____4504
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_f
                                                                 in
                                                              mk_repr a
                                                                uu____4504
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____4503
                                                             in
                                                          let uu____4505 =
                                                            let uu____4514 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_g
                                                               in
                                                            let uu____4521 =
                                                              let uu____4530
                                                                =
                                                                let uu____4537
                                                                  =
                                                                  let uu____4538
                                                                    =
                                                                    let uu____4547
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____4547]
                                                                     in
                                                                  let uu____4566
                                                                    =
                                                                    let uu____4569
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____4569
                                                                     in
                                                                  FStar_Syntax_Util.arrow
                                                                    uu____4538
                                                                    uu____4566
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____4537
                                                                 in
                                                              [uu____4530]
                                                               in
                                                            uu____4514 ::
                                                              uu____4521
                                                             in
                                                          uu____4496 ::
                                                            uu____4505
                                                           in
                                                        uu____4480 ::
                                                          uu____4487
                                                         in
                                                      FStar_List.append
                                                        maybe_range_arg
                                                        uu____4471
                                                       in
                                                    FStar_List.append
                                                      uu____4412 uu____4462
                                                     in
                                                  let uu____4614 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      res
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____4403 uu____4614
                                                   in
                                                let uu____4617 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env2 expected_k
                                                   in
                                                (match uu____4617 with
                                                 | (expected_k1,uu____4625,uu____4626)
                                                     ->
                                                     let env3 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env2
                                                         (FStar_Pervasives_Native.snd
                                                            ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                        in
                                                     let env4 =
                                                       let uu___466_4633 =
                                                         env3  in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.is_pattern
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.is_pattern);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.instantiate_imp);
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           = true;
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.nbe);
                                                         FStar_TypeChecker_Env.strict_args_tab
                                                           =
                                                           (uu___466_4633.FStar_TypeChecker_Env.strict_args_tab)
                                                       }  in
                                                     let br =
                                                       check_and_gen' env4
                                                         ed2.FStar_Syntax_Syntax.bind_repr
                                                         expected_k1
                                                        in
                                                     br)
                                             in
                                          let return_repr =
                                            let x_a =
                                              let uu____4646 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____4646
                                               in
                                            let res =
                                              let wp =
                                                let uu____4654 =
                                                  let uu____4659 =
                                                    let uu____4660 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        return_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____4660
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____4669 =
                                                    let uu____4670 =
                                                      let uu____4673 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      let uu____4674 =
                                                        let uu____4677 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        [uu____4677]  in
                                                      uu____4673 ::
                                                        uu____4674
                                                       in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____4670
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____4659 uu____4669
                                                   in
                                                uu____4654
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr a wp  in
                                            let expected_k =
                                              let uu____4689 =
                                                let uu____4698 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____4705 =
                                                  let uu____4714 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x_a
                                                     in
                                                  [uu____4714]  in
                                                uu____4698 :: uu____4705  in
                                              let uu____4739 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____4689 uu____4739
                                               in
                                            let uu____4742 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k
                                               in
                                            match uu____4742 with
                                            | (expected_k1,uu____4750,uu____4751)
                                                ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env2
                                                    (FStar_Pervasives_Native.snd
                                                       ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                   in
                                                let uu____4757 =
                                                  check_and_gen' env3
                                                    ed2.FStar_Syntax_Syntax.return_repr
                                                    expected_k1
                                                   in
                                                (match uu____4757 with
                                                 | (univs1,repr1) ->
                                                     (match univs1 with
                                                      | [] -> ([], repr1)
                                                      | uu____4780 ->
                                                          FStar_Errors.raise_error
                                                            (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                              "Unexpected universe-polymorphic return for effect")
                                                            repr1.FStar_Syntax_Syntax.pos))
                                             in
                                          let actions =
                                            let check_action act =
                                              let uu____4795 =
                                                if
                                                  act.FStar_Syntax_Syntax.action_univs
                                                    = []
                                                then (env2, act)
                                                else
                                                  (let uu____4809 =
                                                     FStar_Syntax_Subst.univ_var_opening
                                                       act.FStar_Syntax_Syntax.action_univs
                                                      in
                                                   match uu____4809 with
                                                   | (usubst,uvs) ->
                                                       let uu____4832 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env2 uvs
                                                          in
                                                       let uu____4833 =
                                                         let uu___495_4834 =
                                                           act  in
                                                         let uu____4835 =
                                                           FStar_Syntax_Subst.subst_binders
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_params
                                                            in
                                                         let uu____4836 =
                                                           FStar_Syntax_Subst.subst
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____4837 =
                                                           FStar_Syntax_Subst.subst
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_typ
                                                            in
                                                         {
                                                           FStar_Syntax_Syntax.action_name
                                                             =
                                                             (uu___495_4834.FStar_Syntax_Syntax.action_name);
                                                           FStar_Syntax_Syntax.action_unqualified_name
                                                             =
                                                             (uu___495_4834.FStar_Syntax_Syntax.action_unqualified_name);
                                                           FStar_Syntax_Syntax.action_univs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.action_params
                                                             = uu____4835;
                                                           FStar_Syntax_Syntax.action_defn
                                                             = uu____4836;
                                                           FStar_Syntax_Syntax.action_typ
                                                             = uu____4837
                                                         }  in
                                                       (uu____4832,
                                                         uu____4833))
                                                 in
                                              match uu____4795 with
                                              | (env3,act1) ->
                                                  let act_typ =
                                                    let uu____4841 =
                                                      let uu____4842 =
                                                        FStar_Syntax_Subst.compress
                                                          act1.FStar_Syntax_Syntax.action_typ
                                                         in
                                                      uu____4842.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____4841 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,c) ->
                                                        let c1 =
                                                          FStar_Syntax_Util.comp_to_comp_typ
                                                            c
                                                           in
                                                        let uu____4868 =
                                                          FStar_Ident.lid_equals
                                                            c1.FStar_Syntax_Syntax.effect_name
                                                            ed2.FStar_Syntax_Syntax.mname
                                                           in
                                                        if uu____4868
                                                        then
                                                          let uu____4871 =
                                                            let uu____4874 =
                                                              let uu____4875
                                                                =
                                                                let uu____4876
                                                                  =
                                                                  FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____4876
                                                                 in
                                                              mk_repr'
                                                                c1.FStar_Syntax_Syntax.result_typ
                                                                uu____4875
                                                               in
                                                            FStar_Syntax_Syntax.mk_Total
                                                              uu____4874
                                                             in
                                                          FStar_Syntax_Util.arrow
                                                            bs uu____4871
                                                        else
                                                          act1.FStar_Syntax_Syntax.action_typ
                                                    | uu____4899 ->
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  let uu____4900 =
                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                      env3 act_typ
                                                     in
                                                  (match uu____4900 with
                                                   | (act_typ1,uu____4908,g_t)
                                                       ->
                                                       let env' =
                                                         let uu___512_4911 =
                                                           FStar_TypeChecker_Env.set_expected_typ
                                                             env3 act_typ1
                                                            in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             = false;
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.lax);
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.nbe);
                                                           FStar_TypeChecker_Env.strict_args_tab
                                                             =
                                                             (uu___512_4911.FStar_TypeChecker_Env.strict_args_tab)
                                                         }  in
                                                       ((let uu____4914 =
                                                           FStar_TypeChecker_Env.debug
                                                             env3
                                                             (FStar_Options.Other
                                                                "ED")
                                                            in
                                                         if uu____4914
                                                         then
                                                           let uu____4918 =
                                                             FStar_Ident.text_of_lid
                                                               act1.FStar_Syntax_Syntax.action_name
                                                              in
                                                           let uu____4920 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act1.FStar_Syntax_Syntax.action_defn
                                                              in
                                                           let uu____4922 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ1
                                                              in
                                                           FStar_Util.print3
                                                             "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                             uu____4918
                                                             uu____4920
                                                             uu____4922
                                                         else ());
                                                        (let uu____4927 =
                                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                             env'
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         match uu____4927
                                                         with
                                                         | (act_defn,uu____4935,g_a)
                                                             ->
                                                             let act_defn1 =
                                                               FStar_TypeChecker_Normalize.normalize
                                                                 [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant]
                                                                 env3
                                                                 act_defn
                                                                in
                                                             let act_typ2 =
                                                               FStar_TypeChecker_Normalize.normalize
                                                                 [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant;
                                                                 FStar_TypeChecker_Env.Eager_unfolding;
                                                                 FStar_TypeChecker_Env.Beta]
                                                                 env3
                                                                 act_typ1
                                                                in
                                                             let uu____4939 =
                                                               let act_typ3 =
                                                                 FStar_Syntax_Subst.compress
                                                                   act_typ2
                                                                  in
                                                               match 
                                                                 act_typ3.FStar_Syntax_Syntax.n
                                                               with
                                                               | FStar_Syntax_Syntax.Tm_arrow
                                                                   (bs,c) ->
                                                                   let uu____4975
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                   (match uu____4975
                                                                    with
                                                                    | 
                                                                    (bs1,uu____4987)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____4994
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____4994
                                                                     in
                                                                    let uu____4997
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____4997
                                                                    with
                                                                    | 
                                                                    (k1,uu____5011,g)
                                                                    ->
                                                                    (k1, g)))
                                                               | uu____5015
                                                                   ->
                                                                   let uu____5016
                                                                    =
                                                                    let uu____5022
                                                                    =
                                                                    let uu____5024
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____5026
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____5024
                                                                    uu____5026
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____5022)
                                                                     in
                                                                   FStar_Errors.raise_error
                                                                    uu____5016
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                in
                                                             (match uu____4939
                                                              with
                                                              | (expected_k,g_k)
                                                                  ->
                                                                  let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env3
                                                                    act_typ2
                                                                    expected_k
                                                                     in
                                                                  ((let uu____5044
                                                                    =
                                                                    let uu____5045
                                                                    =
                                                                    let uu____5046
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____5046
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____5045
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env3
                                                                    uu____5044);
                                                                   (let act_typ3
                                                                    =
                                                                    let uu____5048
                                                                    =
                                                                    let uu____5049
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____5049.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5048
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____5074
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____5074
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____5081
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____5081
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____5101
                                                                    =
                                                                    let uu____5102
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____5102]
                                                                     in
                                                                    let uu____5103
                                                                    =
                                                                    let uu____5114
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____5114]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____5101;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____5103;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____5139
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____5139))
                                                                    | 
                                                                    uu____5142
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____5144
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env3
                                                                    act_defn1
                                                                    else
                                                                    (let uu____5166
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____5166))
                                                                     in
                                                                    match uu____5144
                                                                    with
                                                                    | 
                                                                    (univs1,act_defn2)
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
                                                                    let uu___562_5185
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___562_5185.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___562_5185.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___562_5185.FStar_Syntax_Syntax.action_params);
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
                                       in
                                    (match uu____3854 with
                                     | (repr,bind_repr,return_repr,actions)
                                         ->
                                         let t0 =
                                           let uu____5209 =
                                             FStar_Syntax_Syntax.mk_Total
                                               ed2.FStar_Syntax_Syntax.signature
                                              in
                                           FStar_Syntax_Util.arrow
                                             ed2.FStar_Syntax_Syntax.binders
                                             uu____5209
                                            in
                                         let uu____5212 =
                                           let uu____5217 =
                                             FStar_TypeChecker_Util.generalize_universes
                                               env0 t0
                                              in
                                           match uu____5217 with
                                           | (gen_univs,t) ->
                                               (match annotated_univ_names
                                                with
                                                | [] -> (gen_univs, t)
                                                | uu____5236 ->
                                                    let uu____5239 =
                                                      ((FStar_List.length
                                                          gen_univs)
                                                         =
                                                         (FStar_List.length
                                                            annotated_univ_names))
                                                        &&
                                                        (FStar_List.forall2
                                                           (fun u1  ->
                                                              fun u2  ->
                                                                let uu____5246
                                                                  =
                                                                  FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2
                                                                   in
                                                                uu____5246 =
                                                                  Prims.int_zero)
                                                           gen_univs
                                                           annotated_univ_names)
                                                       in
                                                    if uu____5239
                                                    then (gen_univs, t)
                                                    else
                                                      (let uu____5257 =
                                                         let uu____5263 =
                                                           let uu____5265 =
                                                             FStar_Util.string_of_int
                                                               (FStar_List.length
                                                                  annotated_univ_names)
                                                              in
                                                           let uu____5267 =
                                                             FStar_Util.string_of_int
                                                               (FStar_List.length
                                                                  gen_univs)
                                                              in
                                                           FStar_Util.format2
                                                             "Expected an effect definition with %s universes; but found %s"
                                                             uu____5265
                                                             uu____5267
                                                            in
                                                         (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                           uu____5263)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____5257
                                                         (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                            in
                                         (match uu____5212 with
                                          | (univs1,t) ->
                                              let signature1 =
                                                let uu____5278 =
                                                  let uu____5291 =
                                                    let uu____5292 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____5292.FStar_Syntax_Syntax.n
                                                     in
                                                  (effect_params, uu____5291)
                                                   in
                                                match uu____5278 with
                                                | ([],uu____5303) -> t
                                                | (uu____5318,FStar_Syntax_Syntax.Tm_arrow
                                                   (uu____5319,c)) ->
                                                    FStar_Syntax_Util.comp_result
                                                      c
                                                | uu____5357 ->
                                                    failwith
                                                      "Impossible : t is an arrow"
                                                 in
                                              let close1 n1 ts =
                                                let ts1 =
                                                  let uu____5385 =
                                                    FStar_Syntax_Subst.close_tscheme
                                                      effect_params ts
                                                     in
                                                  FStar_Syntax_Subst.close_univ_vars_tscheme
                                                    univs1 uu____5385
                                                   in
                                                let m =
                                                  FStar_List.length
                                                    (FStar_Pervasives_Native.fst
                                                       ts1)
                                                   in
                                                (let uu____5392 =
                                                   ((n1 >= Prims.int_zero) &&
                                                      (let uu____5396 =
                                                         FStar_Syntax_Util.is_unknown
                                                           (FStar_Pervasives_Native.snd
                                                              ts1)
                                                          in
                                                       Prims.op_Negation
                                                         uu____5396))
                                                     && (m <> n1)
                                                    in
                                                 if uu____5392
                                                 then
                                                   let error =
                                                     if m < n1
                                                     then
                                                       "not universe-polymorphic enough"
                                                     else
                                                       "too universe-polymorphic"
                                                      in
                                                   let err_msg =
                                                     let uu____5414 =
                                                       FStar_Util.string_of_int
                                                         m
                                                        in
                                                     let uu____5416 =
                                                       FStar_Util.string_of_int
                                                         n1
                                                        in
                                                     let uu____5418 =
                                                       FStar_Syntax_Print.tscheme_to_string
                                                         ts1
                                                        in
                                                     FStar_Util.format4
                                                       "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                       error uu____5414
                                                       uu____5416 uu____5418
                                                      in
                                                   FStar_Errors.raise_error
                                                     (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                       err_msg)
                                                     (FStar_Pervasives_Native.snd
                                                        ts1).FStar_Syntax_Syntax.pos
                                                 else ());
                                                ts1  in
                                              let close_action act =
                                                let uu____5434 =
                                                  close1 (~- Prims.int_one)
                                                    ((act.FStar_Syntax_Syntax.action_univs),
                                                      (act.FStar_Syntax_Syntax.action_defn))
                                                   in
                                                match uu____5434 with
                                                | (univs2,defn) ->
                                                    let uu____5450 =
                                                      close1
                                                        (~- Prims.int_one)
                                                        ((act.FStar_Syntax_Syntax.action_univs),
                                                          (act.FStar_Syntax_Syntax.action_typ))
                                                       in
                                                    (match uu____5450 with
                                                     | (univs',typ) ->
                                                         let uu___612_5467 =
                                                           act  in
                                                         {
                                                           FStar_Syntax_Syntax.action_name
                                                             =
                                                             (uu___612_5467.FStar_Syntax_Syntax.action_name);
                                                           FStar_Syntax_Syntax.action_unqualified_name
                                                             =
                                                             (uu___612_5467.FStar_Syntax_Syntax.action_unqualified_name);
                                                           FStar_Syntax_Syntax.action_univs
                                                             = univs2;
                                                           FStar_Syntax_Syntax.action_params
                                                             =
                                                             (uu___612_5467.FStar_Syntax_Syntax.action_params);
                                                           FStar_Syntax_Syntax.action_defn
                                                             = defn;
                                                           FStar_Syntax_Syntax.action_typ
                                                             = typ
                                                         })
                                                 in
                                              let match_wps =
                                                let uu____5474 =
                                                  let uu____5475 =
                                                    close1 Prims.int_zero
                                                      if_then_else2
                                                     in
                                                  let uu____5477 =
                                                    close1 Prims.int_zero
                                                      ite_wp1
                                                     in
                                                  let uu____5479 =
                                                    close1 Prims.int_one
                                                      close_wp1
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.if_then_else
                                                      = uu____5475;
                                                    FStar_Syntax_Syntax.ite_wp
                                                      = uu____5477;
                                                    FStar_Syntax_Syntax.close_wp
                                                      = uu____5479
                                                  }  in
                                                FStar_Util.Inl uu____5474  in
                                              let ed3 =
                                                let uu___616_5482 = ed2  in
                                                let uu____5483 =
                                                  close1 Prims.int_zero
                                                    return_wp
                                                   in
                                                let uu____5485 =
                                                  close1 Prims.int_one
                                                    bind_wp
                                                   in
                                                let uu____5487 =
                                                  close1 Prims.int_zero
                                                    stronger
                                                   in
                                                let uu____5489 =
                                                  FStar_Util.map_opt
                                                    trivial_wp
                                                    (close1 Prims.int_zero)
                                                   in
                                                let uu____5493 =
                                                  let uu____5494 =
                                                    close1 Prims.int_zero
                                                      ([], repr)
                                                     in
                                                  FStar_Pervasives_Native.snd
                                                    uu____5494
                                                   in
                                                let uu____5512 =
                                                  close1 Prims.int_zero
                                                    return_repr
                                                   in
                                                let uu____5514 =
                                                  close1 Prims.int_one
                                                    bind_repr
                                                   in
                                                let uu____5516 =
                                                  FStar_List.map close_action
                                                    actions
                                                   in
                                                {
                                                  FStar_Syntax_Syntax.is_layered
                                                    =
                                                    (uu___616_5482.FStar_Syntax_Syntax.is_layered);
                                                  FStar_Syntax_Syntax.cattributes
                                                    =
                                                    (uu___616_5482.FStar_Syntax_Syntax.cattributes);
                                                  FStar_Syntax_Syntax.mname =
                                                    (uu___616_5482.FStar_Syntax_Syntax.mname);
                                                  FStar_Syntax_Syntax.univs =
                                                    univs1;
                                                  FStar_Syntax_Syntax.binders
                                                    = effect_params;
                                                  FStar_Syntax_Syntax.signature
                                                    = signature1;
                                                  FStar_Syntax_Syntax.ret_wp
                                                    = uu____5483;
                                                  FStar_Syntax_Syntax.bind_wp
                                                    = uu____5485;
                                                  FStar_Syntax_Syntax.stronger
                                                    = uu____5487;
                                                  FStar_Syntax_Syntax.match_wps
                                                    = match_wps;
                                                  FStar_Syntax_Syntax.trivial
                                                    = uu____5489;
                                                  FStar_Syntax_Syntax.repr =
                                                    uu____5493;
                                                  FStar_Syntax_Syntax.return_repr
                                                    = uu____5512;
                                                  FStar_Syntax_Syntax.bind_repr
                                                    = uu____5514;
                                                  FStar_Syntax_Syntax.stronger_repr
                                                    =
                                                    (uu___616_5482.FStar_Syntax_Syntax.stronger_repr);
                                                  FStar_Syntax_Syntax.actions
                                                    = uu____5516;
                                                  FStar_Syntax_Syntax.eff_attrs
                                                    =
                                                    (uu___616_5482.FStar_Syntax_Syntax.eff_attrs)
                                                }  in
                                              ((let uu____5520 =
                                                  (FStar_TypeChecker_Env.debug
                                                     env2 FStar_Options.Low)
                                                    ||
                                                    (FStar_All.pipe_left
                                                       (FStar_TypeChecker_Env.debug
                                                          env2)
                                                       (FStar_Options.Other
                                                          "ED"))
                                                   in
                                                if uu____5520
                                                then
                                                  let uu____5525 =
                                                    FStar_Syntax_Print.eff_decl_to_string
                                                      false ed3
                                                     in
                                                  FStar_Util.print_string
                                                    uu____5525
                                                else ());
                                               ed3)))))))))
  
let (cps_and_elaborate :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun ed  ->
      let uu____5551 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____5551 with
      | (effect_binders_un,signature_un) ->
          let uu____5568 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____5568 with
           | (effect_binders,env1,uu____5587) ->
               let uu____5588 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____5588 with
                | (signature,uu____5604) ->
                    let raise_error1 uu____5620 =
                      match uu____5620 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____5656  ->
                           match uu____5656 with
                           | (bv,qual) ->
                               let uu____5675 =
                                 let uu___641_5676 = bv  in
                                 let uu____5677 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___641_5676.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___641_5676.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____5677
                                 }  in
                               (uu____5675, qual)) effect_binders
                       in
                    let uu____5682 =
                      let uu____5689 =
                        let uu____5690 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____5690.FStar_Syntax_Syntax.n  in
                      match uu____5689 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____5700)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____5732 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____5682 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____5758 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____5758
                           then
                             let uu____5761 =
                               let uu____5764 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____5764  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____5761
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____5812 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____5812 with
                           | (t2,comp,uu____5825) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____5834 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____5834 with
                          | (repr,_comp) ->
                              ((let uu____5858 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____5858
                                then
                                  let uu____5862 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____5862
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
                                let uu____5869 =
                                  recheck_debug "*" env1 wp_type  in
                                let wp_a =
                                  let uu____5872 =
                                    let uu____5873 =
                                      let uu____5874 =
                                        let uu____5891 =
                                          let uu____5902 =
                                            let uu____5911 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____5914 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____5911, uu____5914)  in
                                          [uu____5902]  in
                                        (wp_type, uu____5891)  in
                                      FStar_Syntax_Syntax.Tm_app uu____5874
                                       in
                                    mk1 uu____5873  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta] env1
                                    uu____5872
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____5962 =
                                      let uu____5969 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____5969)  in
                                    let uu____5975 =
                                      let uu____5984 =
                                        let uu____5991 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____5991
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____5984]  in
                                    uu____5962 :: uu____5975  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let uu____6028 =
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
                                  let uu____6094 = item  in
                                  match uu____6094 with
                                  | (u_item,item1) ->
                                      let uu____6109 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____6109 with
                                       | (item2,item_comp) ->
                                           ((let uu____6125 =
                                               let uu____6127 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____6127
                                                in
                                             if uu____6125
                                             then
                                               let uu____6130 =
                                                 let uu____6136 =
                                                   let uu____6138 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____6140 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____6138 uu____6140
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____6136)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____6130
                                             else ());
                                            (let uu____6146 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____6146 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let uu____6164 =
                                                   recheck_debug "*" env2
                                                     item_wp
                                                    in
                                                 let uu____6166 =
                                                   recheck_debug "_" env2
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab))))
                                   in
                                let uu____6168 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____6168 with
                                | (dmff_env1,uu____6194,bind_wp,bind_elab) ->
                                    let uu____6197 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____6197 with
                                     | (dmff_env2,uu____6223,return_wp,return_elab)
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
                                           let uu____6232 =
                                             let uu____6233 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____6233.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6232 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____6291 =
                                                 let uu____6310 =
                                                   let uu____6315 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____6315
                                                    in
                                                 match uu____6310 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____6397 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____6291 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____6451 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____6451 [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____6474 =
                                                          let uu____6475 =
                                                            let uu____6492 =
                                                              let uu____6503
                                                                =
                                                                let uu____6512
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11)
                                                                   in
                                                                let uu____6517
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____6512,
                                                                  uu____6517)
                                                                 in
                                                              [uu____6503]
                                                               in
                                                            (wp_type,
                                                              uu____6492)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____6475
                                                           in
                                                        mk1 uu____6474  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Env.Beta]
                                                        env0 raw_wp_b1
                                                       in
                                                    let uu____6553 =
                                                      let uu____6562 =
                                                        let uu____6563 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____6563
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____6562
                                                       in
                                                    (match uu____6553 with
                                                     | (bs1,body2,what') ->
                                                         let fail1 uu____6586
                                                           =
                                                           let error_msg =
                                                             let uu____6589 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2
                                                                in
                                                             let uu____6591 =
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
                                                               uu____6589
                                                               uu____6591
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
                                                               ((let uu____6601
                                                                   =
                                                                   let uu____6603
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                   Prims.op_Negation
                                                                    uu____6603
                                                                    in
                                                                 if
                                                                   uu____6601
                                                                 then
                                                                   fail1 ()
                                                                 else ());
                                                                (let uu____6608
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
                                                                   uu____6608
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
                                                             let uu____6637 =
                                                               let uu____6642
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp
                                                                  in
                                                               let uu____6643
                                                                 =
                                                                 let uu____6644
                                                                   =
                                                                   let uu____6653
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                   (uu____6653,
                                                                    FStar_Pervasives_Native.None)
                                                                    in
                                                                 [uu____6644]
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____6642
                                                                 uu____6643
                                                                in
                                                             uu____6637
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange
                                                              in
                                                           let uu____6688 =
                                                             let uu____6689 =
                                                               let uu____6698
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp
                                                                  in
                                                               [uu____6698]
                                                                in
                                                             b11 ::
                                                               uu____6689
                                                              in
                                                           let uu____6723 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what
                                                              in
                                                           FStar_Syntax_Util.abs
                                                             uu____6688
                                                             uu____6723
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____6726 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let return_wp1 =
                                           let uu____6734 =
                                             let uu____6735 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____6735.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6734 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____6793 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____6793
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____6814 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let bind_wp1 =
                                           let uu____6822 =
                                             let uu____6823 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____6823.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6822 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_constant_at_level
                                                      Prims.int_one)
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let uu____6857 =
                                                 let uu____6858 =
                                                   let uu____6867 =
                                                     let uu____6874 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____6874
                                                      in
                                                   [uu____6867]  in
                                                 FStar_List.append uu____6858
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____6857 body what
                                           | uu____6893 ->
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
                                             (let uu____6923 =
                                                let uu____6924 =
                                                  let uu____6925 =
                                                    let uu____6942 =
                                                      let uu____6953 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____6953
                                                       in
                                                    (t, uu____6942)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____6925
                                                   in
                                                mk1 uu____6924  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____6923)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____7011 = f a2  in
                                               [uu____7011]
                                           | x::xs ->
                                               let uu____7022 =
                                                 apply_last1 f xs  in
                                               x :: uu____7022
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
                                           let uu____7056 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____7056 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____7086 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____7086
                                                 then
                                                   let uu____7089 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____7089
                                                 else ());
                                                (let uu____7094 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____7094))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____7103 =
                                                 let uu____7108 = mk_lid name
                                                    in
                                                 let uu____7109 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____7108 uu____7109
                                                  in
                                               (match uu____7103 with
                                                | (sigelt,fv) ->
                                                    ((let uu____7113 =
                                                        let uu____7116 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____7116
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____7113);
                                                     fv))
                                            in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp2 =
                                           register "return_wp" return_wp1
                                            in
                                         ((let uu____7170 =
                                             let uu____7173 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.PushOptions
                                                       (FStar_Pervasives_Native.Some
                                                          "--admit_smt_queries true")))
                                                in
                                             let uu____7176 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____7173 :: uu____7176  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____7170);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           (let uu____7228 =
                                              let uu____7231 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     FStar_Syntax_Syntax.PopOptions)
                                                 in
                                              let uu____7232 =
                                                FStar_ST.op_Bang sigelts  in
                                              uu____7231 :: uu____7232  in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____7228);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            (let uu____7284 =
                                               let uu____7287 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.PushOptions
                                                         (FStar_Pervasives_Native.Some
                                                            "--admit_smt_queries true")))
                                                  in
                                               let uu____7290 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____7287 :: uu____7290  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____7284);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             (let uu____7342 =
                                                let uu____7345 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       FStar_Syntax_Syntax.PopOptions)
                                                   in
                                                let uu____7346 =
                                                  FStar_ST.op_Bang sigelts
                                                   in
                                                uu____7345 :: uu____7346  in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____7342);
                                             (let uu____7395 =
                                                FStar_List.fold_left
                                                  (fun uu____7435  ->
                                                     fun action  ->
                                                       match uu____7435 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____7456 =
                                                             let uu____7463 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____7463
                                                               params_un
                                                              in
                                                           (match uu____7456
                                                            with
                                                            | (action_params,env',uu____7472)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____7498
                                                                     ->
                                                                    match uu____7498
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____7517
                                                                    =
                                                                    let uu___834_7518
                                                                    = bv  in
                                                                    let uu____7519
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___834_7518.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___834_7518.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____7519
                                                                    }  in
                                                                    (uu____7517,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____7525
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____7525
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
                                                                    uu____7564
                                                                    ->
                                                                    let uu____7565
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____7565
                                                                     in
                                                                    ((
                                                                    let uu____7569
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____7569
                                                                    then
                                                                    let uu____7574
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____7577
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____7580
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____7582
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____7574
                                                                    uu____7577
                                                                    uu____7580
                                                                    uu____7582
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
                                                                    let uu____7591
                                                                    =
                                                                    let uu____7594
                                                                    =
                                                                    let uu___856_7595
                                                                    = action
                                                                     in
                                                                    let uu____7596
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____7597
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___856_7595.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___856_7595.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___856_7595.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____7596;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____7597
                                                                    }  in
                                                                    uu____7594
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____7591))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____7395 with
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
                                                      let uu____7641 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____7648 =
                                                        let uu____7657 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____7657]  in
                                                      uu____7641 ::
                                                        uu____7648
                                                       in
                                                    let uu____7682 =
                                                      let uu____7685 =
                                                        let uu____7686 =
                                                          let uu____7687 =
                                                            let uu____7704 =
                                                              let uu____7715
                                                                =
                                                                let uu____7724
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____7727
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____7724,
                                                                  uu____7727)
                                                                 in
                                                              [uu____7715]
                                                               in
                                                            (repr,
                                                              uu____7704)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____7687
                                                           in
                                                        mk1 uu____7686  in
                                                      let uu____7763 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____7685
                                                        uu____7763
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____7682
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let uu____7764 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr2 =
                                                    register "repr" repr1  in
                                                  let uu____7768 =
                                                    let uu____7777 =
                                                      let uu____7778 =
                                                        let uu____7781 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____7781
                                                         in
                                                      uu____7778.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____7777 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____7795)
                                                        ->
                                                        let uu____7832 =
                                                          let uu____7853 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____7853
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____7921 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____7832
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____7986 =
                                                               let uu____7987
                                                                 =
                                                                 let uu____7990
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____7990
                                                                  in
                                                               uu____7987.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____7986
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____8023
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____8023
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____8038
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____8069
                                                                     ->
                                                                    match uu____8069
                                                                    with
                                                                    | 
                                                                    (bv,uu____8078)
                                                                    ->
                                                                    let uu____8083
                                                                    =
                                                                    let uu____8085
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____8085
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____8083
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____8038
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
                                                                    let uu____8177
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____8177
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____8187
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____8198
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____8198
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____8208
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____8211
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____8208,
                                                                    uu____8211)))
                                                              | uu____8226 ->
                                                                  let uu____8227
                                                                    =
                                                                    let uu____8233
                                                                    =
                                                                    let uu____8235
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____8235
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____8233)
                                                                     in
                                                                  raise_error1
                                                                    uu____8227))
                                                    | uu____8247 ->
                                                        let uu____8248 =
                                                          let uu____8254 =
                                                            let uu____8256 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type
                                                               in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____8256
                                                             in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____8254)
                                                           in
                                                        raise_error1
                                                          uu____8248
                                                     in
                                                  (match uu____7768 with
                                                   | (pre,post) ->
                                                       ((let uu____8289 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____8292 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____8295 =
                                                           register "wp"
                                                             wp_type
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___912_8298
                                                             = ed  in
                                                           let uu____8299 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____8300 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature
                                                              in
                                                           let uu____8301 =
                                                             let uu____8302 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____8302)
                                                              in
                                                           let uu____8309 =
                                                             let uu____8310 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____8310)
                                                              in
                                                           let uu____8317 =
                                                             apply_close
                                                               repr2
                                                              in
                                                           let uu____8318 =
                                                             let uu____8319 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____8319)
                                                              in
                                                           let uu____8326 =
                                                             let uu____8327 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____8327)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.is_layered
                                                               =
                                                               (uu___912_8298.FStar_Syntax_Syntax.is_layered);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___912_8298.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___912_8298.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___912_8298.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____8299;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____8300;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____8301;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____8309;
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___912_8298.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.match_wps
                                                               =
                                                               (uu___912_8298.FStar_Syntax_Syntax.match_wps);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___912_8298.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____8317;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____8318;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____8326;
                                                             FStar_Syntax_Syntax.stronger_repr
                                                               =
                                                               (uu___912_8298.FStar_Syntax_Syntax.stronger_repr);
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___912_8298.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____8334 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____8334
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____8352
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____8352
                                                               then
                                                                 let uu____8356
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____8356
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
                                                                    let uu____8376
                                                                    =
                                                                    let uu____8379
                                                                    =
                                                                    let uu____8380
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____8380)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____8379
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
                                                                    uu____8376;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____8387
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____8387
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____8390
                                                                 =
                                                                 let uu____8393
                                                                   =
                                                                   let uu____8396
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____8396
                                                                    in
                                                                 FStar_List.append
                                                                   uu____8393
                                                                   sigelts'
                                                                  in
                                                               (uu____8390,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____8437 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____8437 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____8472 = FStar_List.hd ses  in
            uu____8472.FStar_Syntax_Syntax.sigrng  in
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
           | uu____8477 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____8483,[],t,uu____8485,uu____8486);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____8488;
               FStar_Syntax_Syntax.sigattrs = uu____8489;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____8491,_t_top,_lex_t_top,_8525,uu____8494);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____8496;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____8497;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____8499,_t_cons,_lex_t_cons,_8533,uu____8502);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____8504;
                 FStar_Syntax_Syntax.sigattrs = uu____8505;_}::[]
               when
               ((_8525 = Prims.int_zero) && (_8533 = Prims.int_zero)) &&
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
                 let uu____8558 =
                   let uu____8565 =
                     let uu____8566 =
                       let uu____8573 =
                         let uu____8576 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____8576
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____8573, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____8566  in
                   FStar_Syntax_Syntax.mk uu____8565  in
                 uu____8558 FStar_Pervasives_Native.None r1  in
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
                   let uu____8591 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____8591
                    in
                 let hd1 =
                   let uu____8593 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____8593
                    in
                 let tl1 =
                   let uu____8595 =
                     let uu____8596 =
                       let uu____8603 =
                         let uu____8604 =
                           let uu____8611 =
                             let uu____8614 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____8614
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____8611, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____8604  in
                       FStar_Syntax_Syntax.mk uu____8603  in
                     uu____8596 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____8595
                    in
                 let res =
                   let uu____8620 =
                     let uu____8627 =
                       let uu____8628 =
                         let uu____8635 =
                           let uu____8638 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____8638
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____8635,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____8628  in
                     FStar_Syntax_Syntax.mk uu____8627  in
                   uu____8620 FStar_Pervasives_Native.None r2  in
                 let uu____8641 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____8641
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
               let uu____8680 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____8680;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____8685 ->
               let err_msg =
                 let uu____8690 =
                   let uu____8692 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____8692  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____8690
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
    fun uu____8717  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____8717 with
          | (uvs,t) ->
              let uu____8730 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____8730 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____8742 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____8742 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____8760 =
                        let uu____8763 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____8763
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____8760)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____8786 =
          let uu____8787 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____8787 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____8786 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____8812 =
          let uu____8813 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____8813 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____8812 r
  
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
          (let uu____8862 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____8862
           then
             let uu____8865 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____8865
           else ());
          (let uu____8870 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____8870 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____8901 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____8901 FStar_List.flatten  in
               ((let uu____8915 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____8918 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____8918)
                    in
                 if uu____8915
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
                           let uu____8934 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____8944,uu____8945,uu____8946,uu____8947,uu____8948)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____8957 -> failwith "Impossible!"  in
                           match uu____8934 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Inductive type "
                                      (Prims.op_Hat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____8976 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____8986,uu____8987,ty_lid,uu____8989,uu____8990)
                               -> (data_lid, ty_lid)
                           | uu____8997 -> failwith "Impossible"  in
                         match uu____8976 with
                         | (data_lid,ty_lid) ->
                             let uu____9005 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____9008 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____9008)
                                in
                             if uu____9005
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Exception "
                                      (Prims.op_Hat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____9022 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____9027,uu____9028,uu____9029,uu____9030,uu____9031)
                         -> lid
                     | uu____9040 -> failwith "Impossible"  in
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
                   let uu____9058 =
                     (((FStar_List.length tcs) = Prims.int_zero) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____9058
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
          let pop1 uu____9133 =
            let uu____9134 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___1090_9144  ->
               match () with
               | () ->
                   let uu____9151 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____9151 (fun r  -> pop1 (); r)) ()
          with | uu___1089_9182 -> (pop1 (); FStar_Exn.raise uu___1089_9182)
  
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
      | uu____9498 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____9556 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____9556 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____9581 .
    'Auu____9581 FStar_Pervasives_Native.option -> 'Auu____9581 Prims.list
  =
  fun uu___0_9590  ->
    match uu___0_9590 with
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
            let uu____9670 = collect1 tl1  in
            (match uu____9670 with
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
        | ((e,n1)::uu____9908,[]) ->
            FStar_Pervasives_Native.Some (e, n1, Prims.int_zero)
        | ([],(e,n1)::uu____9964) ->
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
          let uu____10174 =
            let uu____10176 = FStar_Options.ide ()  in
            Prims.op_Negation uu____10176  in
          if uu____10174
          then
            let uu____10179 =
              let uu____10184 = FStar_TypeChecker_Env.dsenv env  in
              let uu____10185 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____10184 uu____10185  in
            (match uu____10179 with
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
                              let uu____10218 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____10219 =
                                let uu____10225 =
                                  let uu____10227 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____10229 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____10227 uu____10229
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____10225)
                                 in
                              FStar_Errors.log_issue uu____10218 uu____10219
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____10236 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____10237 =
                                   let uu____10243 =
                                     let uu____10245 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____10245
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____10243)
                                    in
                                 FStar_Errors.log_issue uu____10236
                                   uu____10237)
                              else ())
                         else ())))
          else ()
      | uu____10255 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____10300 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____10328 ->
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
             let uu____10388 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____10388
             then
               let ses1 =
                 let uu____10396 =
                   let uu____10397 =
                     let uu____10398 =
                       tc_inductive
                         (let uu___1222_10407 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1222_10407.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1222_10407.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1222_10407.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1222_10407.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1222_10407.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1222_10407.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1222_10407.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1222_10407.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1222_10407.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1222_10407.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1222_10407.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1222_10407.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1222_10407.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1222_10407.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1222_10407.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1222_10407.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1222_10407.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1222_10407.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1222_10407.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1222_10407.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1222_10407.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___1222_10407.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1222_10407.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1222_10407.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1222_10407.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1222_10407.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1222_10407.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1222_10407.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1222_10407.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1222_10407.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1222_10407.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1222_10407.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1222_10407.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1222_10407.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1222_10407.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1222_10407.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1222_10407.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1222_10407.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1222_10407.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1222_10407.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1222_10407.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1222_10407.FStar_TypeChecker_Env.strict_args_tab)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____10398
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____10397
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____10396
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____10421 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____10421
                 then
                   let uu____10426 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1226_10430 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1226_10430.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1226_10430.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1226_10430.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1226_10430.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____10426
                 else ());
                ses1)
             else ses  in
           let uu____10440 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____10440 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___1233_10464 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1233_10464.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1233_10464.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1233_10464.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1233_10464.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____10476 = cps_and_elaborate env ne  in
           (match uu____10476 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___1247_10515 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1247_10515.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1247_10515.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1247_10515.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1247_10515.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___1250_10517 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1250_10517.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1250_10517.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1250_10517.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1250_10517.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses), env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           ((let uu____10524 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "LayeredEffects")
                in
             if uu____10524
             then
               let uu____10529 = FStar_Syntax_Print.sigelt_to_string se  in
               FStar_Util.print1
                 "Starting to typecheck layered effect:\n%s\n" uu____10529
             else ());
            (let tc_fun =
               if ne.FStar_Syntax_Syntax.is_layered
               then tc_layered_eff_decl
               else tc_eff_decl  in
             let ne1 =
               let uu____10553 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env)
                  in
               if uu____10553
               then
                 let ne1 =
                   let uu____10557 =
                     let uu____10558 =
                       let uu____10559 =
                         tc_fun
                           (let uu___1260_10562 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1260_10562.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1260_10562.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1260_10562.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1260_10562.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1260_10562.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1260_10562.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1260_10562.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1260_10562.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1260_10562.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1260_10562.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1260_10562.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1260_10562.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1260_10562.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1260_10562.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1260_10562.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1260_10562.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1260_10562.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1260_10562.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1260_10562.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1260_10562.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1260_10562.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 = true;
                              FStar_TypeChecker_Env.failhard =
                                (uu___1260_10562.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1260_10562.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1260_10562.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1260_10562.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1260_10562.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1260_10562.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1260_10562.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1260_10562.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1260_10562.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1260_10562.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1260_10562.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1260_10562.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1260_10562.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1260_10562.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1260_10562.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1260_10562.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1260_10562.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1260_10562.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1260_10562.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1260_10562.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1260_10562.FStar_TypeChecker_Env.strict_args_tab)
                            }) ne
                          in
                       FStar_All.pipe_right uu____10559
                         (fun ne1  ->
                            let uu___1263_10568 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_new_effect ne1);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___1263_10568.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___1263_10568.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___1263_10568.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___1263_10568.FStar_Syntax_Syntax.sigattrs)
                            })
                        in
                     FStar_All.pipe_right uu____10558
                       (FStar_TypeChecker_Normalize.elim_uvars env)
                      in
                   FStar_All.pipe_right uu____10557
                     FStar_Syntax_Util.eff_decl_of_new_effect
                    in
                 ((let uu____10570 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "TwoPhases")
                      in
                   if uu____10570
                   then
                     let uu____10575 =
                       FStar_Syntax_Print.sigelt_to_string
                         (let uu___1267_10579 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1267_10579.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1267_10579.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1267_10579.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1267_10579.FStar_Syntax_Syntax.sigattrs)
                          })
                        in
                     FStar_Util.print1 "Effect decl after phase 1: %s\n"
                       uu____10575
                   else ());
                  ne1)
               else ne  in
             let ne2 = tc_fun env ne1  in
             let se1 =
               let uu___1272_10587 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_new_effect ne2);
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1272_10587.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1272_10587.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1272_10587.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1272_10587.FStar_Syntax_Syntax.sigattrs)
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
           let uu____10595 =
             let uu____10602 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____10602
              in
           (match uu____10595 with
            | (a,wp_a_src) ->
                let uu____10619 =
                  let uu____10626 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____10626
                   in
                (match uu____10619 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____10644 =
                         let uu____10647 =
                           let uu____10648 =
                             let uu____10655 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____10655)  in
                           FStar_Syntax_Syntax.NT uu____10648  in
                         [uu____10647]  in
                       FStar_Syntax_Subst.subst uu____10644 wp_b_tgt  in
                     let expected_k =
                       let uu____10663 =
                         let uu____10672 = FStar_Syntax_Syntax.mk_binder a
                            in
                         let uu____10679 =
                           let uu____10688 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____10688]  in
                         uu____10672 :: uu____10679  in
                       let uu____10713 =
                         FStar_Syntax_Syntax.mk_Total wp_a_tgt  in
                       FStar_Syntax_Util.arrow uu____10663 uu____10713  in
                     let repr_type eff_name a1 wp =
                       (let uu____10735 =
                          let uu____10737 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name
                             in
                          Prims.op_Negation uu____10737  in
                        if uu____10735
                        then
                          let uu____10740 =
                            let uu____10746 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____10746)
                             in
                          let uu____10750 =
                            FStar_TypeChecker_Env.get_range env  in
                          FStar_Errors.raise_error uu____10740 uu____10750
                        else ());
                       (let uu____10753 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name
                           in
                        match uu____10753 with
                        | FStar_Pervasives_Native.None  ->
                            failwith
                              "internal error: reifiable effect has no decl?"
                        | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                            let repr =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [FStar_Syntax_Syntax.U_unknown] env ed
                                ([], (ed.FStar_Syntax_Syntax.repr))
                               in
                            let uu____10790 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____10791 =
                              let uu____10798 =
                                let uu____10799 =
                                  let uu____10816 =
                                    let uu____10827 =
                                      FStar_Syntax_Syntax.as_arg a1  in
                                    let uu____10836 =
                                      let uu____10847 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____10847]  in
                                    uu____10827 :: uu____10836  in
                                  (repr, uu____10816)  in
                                FStar_Syntax_Syntax.Tm_app uu____10799  in
                              FStar_Syntax_Syntax.mk uu____10798  in
                            uu____10791 FStar_Pervasives_Native.None
                              uu____10790)
                        in
                     let uu____10892 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____11065 =
                             if (FStar_List.length uvs) > Prims.int_zero
                             then
                               let uu____11076 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____11076 with
                               | (usubst,uvs1) ->
                                   let uu____11099 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____11100 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____11099, uu____11100)
                             else (env, lift_wp)  in
                           (match uu____11065 with
                            | (env1,lift_wp1) ->
                                let lift_wp2 =
                                  if (FStar_List.length uvs) = Prims.int_zero
                                  then check_and_gen env1 lift_wp1 expected_k
                                  else
                                    (let lift_wp2 =
                                       tc_check_trivial_guard env1 lift_wp1
                                         expected_k
                                        in
                                     let uu____11150 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____11150))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____11221 =
                             if (FStar_List.length what) > Prims.int_zero
                             then
                               let uu____11236 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____11236 with
                               | (usubst,uvs) ->
                                   let uu____11261 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____11261)
                             else ([], lift)  in
                           (match uu____11221 with
                            | (uvs,lift1) ->
                                ((let uu____11297 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____11297
                                  then
                                    let uu____11301 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____11301
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____11307 =
                                    let uu____11314 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____11314 lift1
                                     in
                                  match uu____11307 with
                                  | (lift2,comp,uu____11339) ->
                                      let uu____11340 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____11340 with
                                       | (uu____11369,lift_wp,lift_elab) ->
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
                                             let uu____11401 =
                                               let uu____11412 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____11412
                                                in
                                             let uu____11429 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____11401, uu____11429)
                                           else
                                             (let uu____11458 =
                                                let uu____11469 =
                                                  let uu____11478 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____11478)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____11469
                                                 in
                                              let uu____11493 =
                                                let uu____11502 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____11502)  in
                                              (uu____11458, uu____11493))))))
                        in
                     (match uu____10892 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___1348_11576 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1348_11576.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1348_11576.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1348_11576.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1348_11576.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1348_11576.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1348_11576.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1348_11576.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1348_11576.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1348_11576.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1348_11576.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1348_11576.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1348_11576.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1348_11576.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1348_11576.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1348_11576.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1348_11576.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1348_11576.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1348_11576.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1348_11576.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1348_11576.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1348_11576.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1348_11576.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1348_11576.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1348_11576.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1348_11576.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1348_11576.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1348_11576.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1348_11576.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1348_11576.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1348_11576.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1348_11576.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1348_11576.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1348_11576.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1348_11576.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1348_11576.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1348_11576.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1348_11576.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1348_11576.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1348_11576.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1348_11576.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1348_11576.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1348_11576.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1348_11576.FStar_TypeChecker_Env.strict_args_tab)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____11633 =
                                  let uu____11638 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____11638 with
                                  | (usubst,uvs1) ->
                                      let uu____11661 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____11662 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____11661, uu____11662)
                                   in
                                (match uu____11633 with
                                 | (env2,lift2) ->
                                     let uu____11675 =
                                       let uu____11682 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____11682
                                        in
                                     (match uu____11675 with
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
                                              let uu____11716 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____11717 =
                                                let uu____11724 =
                                                  let uu____11725 =
                                                    let uu____11742 =
                                                      let uu____11753 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____11762 =
                                                        let uu____11773 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____11773]  in
                                                      uu____11753 ::
                                                        uu____11762
                                                       in
                                                    (lift_wp1, uu____11742)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____11725
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____11724
                                                 in
                                              uu____11717
                                                FStar_Pervasives_Native.None
                                                uu____11716
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____11821 =
                                              let uu____11830 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____11837 =
                                                let uu____11846 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____11853 =
                                                  let uu____11862 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____11862]  in
                                                uu____11846 :: uu____11853
                                                 in
                                              uu____11830 :: uu____11837  in
                                            let uu____11893 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____11821 uu____11893
                                             in
                                          let uu____11896 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____11896 with
                                           | (expected_k2,uu____11914,uu____11915)
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
                                                    let uu____11939 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____11939))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____11955 =
                              let uu____11957 =
                                let uu____11959 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____11959
                                  FStar_List.length
                                 in
                              uu____11957 <> Prims.int_one  in
                            if uu____11955
                            then
                              let uu____11981 =
                                let uu____11987 =
                                  let uu____11989 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____11991 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____11993 =
                                    let uu____11995 =
                                      let uu____11997 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____11997
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____11995
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____11989 uu____11991 uu____11993
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____11987)
                                 in
                              FStar_Errors.raise_error uu____11981 r
                            else ());
                           (let uu____12024 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____12035 =
                                   let uu____12037 =
                                     let uu____12040 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____12040
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____12037
                                     FStar_List.length
                                    in
                                 uu____12035 <> Prims.int_one)
                               in
                            if uu____12024
                            then
                              let uu____12094 =
                                let uu____12100 =
                                  let uu____12102 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____12104 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____12106 =
                                    let uu____12108 =
                                      let uu____12110 =
                                        let uu____12113 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____12113
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____12110
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____12108
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____12102 uu____12104 uu____12106
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____12100)
                                 in
                              FStar_Errors.raise_error uu____12094 r
                            else ());
                           (let sub2 =
                              let uu___1385_12172 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___1385_12172.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___1385_12172.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___1388_12174 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___1388_12174.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___1388_12174.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___1388_12174.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___1388_12174.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let uu____12188 =
             if (FStar_List.length uvs) = Prims.int_zero
             then (env, uvs, tps, c)
             else
               (let uu____12216 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____12216 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____12247 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____12247 c  in
                    let uu____12256 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____12256, uvs1, tps1, c1))
              in
           (match uu____12188 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____12278 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____12278 with
                 | (tps2,c2) ->
                     let uu____12295 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____12295 with
                      | (tps3,env3,us) ->
                          let uu____12315 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____12315 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____12343)::uu____12344 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____12363 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____12371 =
                                   let uu____12373 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____12373  in
                                 if uu____12371
                                 then
                                   let uu____12376 =
                                     let uu____12382 =
                                       let uu____12384 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____12386 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____12384 uu____12386
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____12382)
                                      in
                                   FStar_Errors.raise_error uu____12376 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____12394 =
                                   let uu____12395 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____12395
                                    in
                                 match uu____12394 with
                                 | (uvs2,t) ->
                                     let uu____12426 =
                                       let uu____12431 =
                                         let uu____12444 =
                                           let uu____12445 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____12445.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____12444)  in
                                       match uu____12431 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____12460,c5)) -> ([], c5)
                                       | (uu____12502,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____12541 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____12426 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               Prims.int_one
                                           then
                                             (let uu____12575 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____12575 with
                                              | (uu____12580,t1) ->
                                                  let uu____12582 =
                                                    let uu____12588 =
                                                      let uu____12590 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____12592 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____12596 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____12590
                                                        uu____12592
                                                        uu____12596
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____12588)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____12582 r)
                                           else ();
                                           (let se1 =
                                              let uu___1458_12603 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___1458_12603.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___1458_12603.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___1458_12603.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___1458_12603.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____12610,uu____12611,uu____12612) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_12617  ->
                   match uu___1_12617 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____12620 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____12626,uu____12627) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_12636  ->
                   match uu___1_12636 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____12639 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____12650 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____12650
             then
               let uu____12653 =
                 let uu____12659 =
                   let uu____12661 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____12661
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____12659)
                  in
               FStar_Errors.raise_error uu____12653 r
             else ());
            (let uu____12667 =
               let uu____12676 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____12676
               then
                 let uu____12687 =
                   tc_declare_typ
                     (let uu___1482_12690 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1482_12690.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1482_12690.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1482_12690.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1482_12690.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1482_12690.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1482_12690.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1482_12690.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1482_12690.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1482_12690.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1482_12690.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1482_12690.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1482_12690.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1482_12690.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1482_12690.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1482_12690.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1482_12690.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1482_12690.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1482_12690.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1482_12690.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1482_12690.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1482_12690.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1482_12690.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1482_12690.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1482_12690.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1482_12690.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1482_12690.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1482_12690.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1482_12690.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1482_12690.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1482_12690.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1482_12690.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1482_12690.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1482_12690.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1482_12690.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1482_12690.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1482_12690.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1482_12690.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1482_12690.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1482_12690.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1482_12690.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___1482_12690.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___1482_12690.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1482_12690.FStar_TypeChecker_Env.strict_args_tab)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____12687 with
                 | (uvs1,t1) ->
                     ((let uu____12715 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____12715
                       then
                         let uu____12720 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____12722 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____12720 uu____12722
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____12667 with
             | (uvs1,t1) ->
                 let uu____12757 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____12757 with
                  | (uvs2,t2) ->
                      ([(let uu___1495_12787 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1495_12787.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1495_12787.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1495_12787.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1495_12787.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____12792 =
             let uu____12801 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____12801
             then
               let uu____12812 =
                 tc_assume
                   (let uu___1504_12815 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1504_12815.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1504_12815.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1504_12815.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1504_12815.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1504_12815.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1504_12815.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1504_12815.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1504_12815.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1504_12815.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1504_12815.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1504_12815.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1504_12815.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1504_12815.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1504_12815.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1504_12815.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1504_12815.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1504_12815.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1504_12815.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1504_12815.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1504_12815.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1504_12815.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___1504_12815.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1504_12815.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1504_12815.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1504_12815.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1504_12815.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1504_12815.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1504_12815.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1504_12815.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1504_12815.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1504_12815.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1504_12815.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1504_12815.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1504_12815.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1504_12815.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1504_12815.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1504_12815.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1504_12815.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1504_12815.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1504_12815.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1504_12815.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1504_12815.FStar_TypeChecker_Env.strict_args_tab)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____12812 with
               | (uvs1,t1) ->
                   ((let uu____12841 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____12841
                     then
                       let uu____12846 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12848 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____12846
                         uu____12848
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____12792 with
            | (uvs1,t1) ->
                let uu____12883 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____12883 with
                 | (uvs2,t2) ->
                     ([(let uu___1517_12913 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1517_12913.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1517_12913.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1517_12913.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1517_12913.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____12917 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____12917 with
            | (e1,c,g1) ->
                let uu____12937 =
                  let uu____12944 =
                    let uu____12947 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____12947  in
                  let uu____12948 =
                    let uu____12953 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____12953)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____12944 uu____12948
                   in
                (match uu____12937 with
                 | (e2,uu____12965,g) ->
                     ((let uu____12968 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____12968);
                      (let se1 =
                         let uu___1532_12970 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1532_12970.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1532_12970.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1532_12970.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1532_12970.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____12982 = FStar_Options.debug_any ()  in
             if uu____12982
             then
               let uu____12985 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____12987 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____12985
                 uu____12987
             else ());
            (let uu____12992 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____12992 with
             | (t1,uu____13010,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____13024 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____13024 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____13027 =
                              let uu____13033 =
                                let uu____13035 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____13037 =
                                  let uu____13039 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____13039
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____13035 uu____13037
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____13033)
                               in
                            FStar_Errors.raise_error uu____13027 r
                        | uu____13051 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___1553_13056 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1553_13056.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1553_13056.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1553_13056.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1553_13056.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1553_13056.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1553_13056.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1553_13056.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1553_13056.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1553_13056.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1553_13056.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1553_13056.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1553_13056.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1553_13056.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1553_13056.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1553_13056.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1553_13056.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1553_13056.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1553_13056.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1553_13056.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1553_13056.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___1553_13056.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1553_13056.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1553_13056.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1553_13056.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1553_13056.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1553_13056.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1553_13056.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1553_13056.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1553_13056.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1553_13056.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1553_13056.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1553_13056.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1553_13056.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1553_13056.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1553_13056.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1553_13056.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1553_13056.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1553_13056.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1553_13056.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1553_13056.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1553_13056.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___1553_13056.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1553_13056.FStar_TypeChecker_Env.strict_args_tab)
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
                 let uu____13124 =
                   let uu____13126 =
                     let uu____13135 = drop_logic val_q  in
                     let uu____13138 = drop_logic q'  in
                     (uu____13135, uu____13138)  in
                   match uu____13126 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____13124
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____13165 =
                      let uu____13171 =
                        let uu____13173 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____13175 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____13177 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____13173 uu____13175 uu____13177
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____13171)
                       in
                    FStar_Errors.raise_error uu____13165 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____13214 =
                   let uu____13215 = FStar_Syntax_Subst.compress def  in
                   uu____13215.FStar_Syntax_Syntax.n  in
                 match uu____13214 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____13227,uu____13228) -> binders
                 | uu____13253 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____13265;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____13370) -> val_bs1
                     | (uu____13401,[]) -> val_bs1
                     | ((body_bv,uu____13433)::bt,(val_bv,aqual)::vt) ->
                         let uu____13490 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____13514) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___1622_13528 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___1624_13531 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___1624_13531.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___1622_13528.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1622_13528.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____13490
                      in
                   let uu____13538 =
                     let uu____13545 =
                       let uu____13546 =
                         let uu____13561 = rename_binders1 def_bs val_bs  in
                         (uu____13561, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____13546  in
                     FStar_Syntax_Syntax.mk uu____13545  in
                   uu____13538 FStar_Pervasives_Native.None r1
               | uu____13580 -> typ1  in
             let uu___1630_13581 = lb  in
             let uu____13582 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___1630_13581.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1630_13581.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____13582;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1630_13581.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___1630_13581.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1630_13581.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1630_13581.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____13585 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____13640  ->
                     fun lb  ->
                       match uu____13640 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____13686 =
                             let uu____13698 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____13698 with
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
                                   | uu____13778 ->
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
                                  (let uu____13825 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____13825, quals_opt1)))
                              in
                           (match uu____13686 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____13585 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____13929 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___2_13935  ->
                                match uu___2_13935 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____13940 -> false))
                         in
                      if uu____13929
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____13953 =
                    let uu____13960 =
                      let uu____13961 =
                        let uu____13975 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____13975)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____13961  in
                    FStar_Syntax_Syntax.mk uu____13960  in
                  uu____13953 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___1673_13994 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1673_13994.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1673_13994.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1673_13994.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1673_13994.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1673_13994.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1673_13994.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1673_13994.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1673_13994.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1673_13994.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1673_13994.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1673_13994.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1673_13994.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1673_13994.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1673_13994.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1673_13994.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1673_13994.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1673_13994.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1673_13994.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1673_13994.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1673_13994.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1673_13994.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1673_13994.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1673_13994.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1673_13994.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1673_13994.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1673_13994.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1673_13994.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1673_13994.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1673_13994.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1673_13994.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1673_13994.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1673_13994.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1673_13994.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1673_13994.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1673_13994.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1673_13994.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1673_13994.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1673_13994.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1673_13994.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1673_13994.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1673_13994.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___1673_13994.FStar_TypeChecker_Env.strict_args_tab)
                  }  in
                let e1 =
                  let uu____13997 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____13997
                  then
                    let drop_lbtyp e_lax =
                      let uu____14006 =
                        let uu____14007 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____14007.FStar_Syntax_Syntax.n  in
                      match uu____14006 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____14029 =
                              let uu____14030 = FStar_Syntax_Subst.compress e
                                 in
                              uu____14030.FStar_Syntax_Syntax.n  in
                            match uu____14029 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____14034,lb1::[]),uu____14036) ->
                                let uu____14052 =
                                  let uu____14053 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____14053.FStar_Syntax_Syntax.n  in
                                (match uu____14052 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____14058 -> false)
                            | uu____14060 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___1698_14064 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___1700_14079 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___1700_14079.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___1700_14079.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___1700_14079.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___1700_14079.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___1700_14079.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___1700_14079.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___1698_14064.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___1698_14064.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____14082 -> e_lax  in
                    let uu____14083 =
                      FStar_Util.record_time
                        (fun uu____14091  ->
                           let uu____14092 =
                             let uu____14093 =
                               let uu____14094 =
                                 FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                   (let uu___1704_14103 = env'  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___1704_14103.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___1704_14103.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___1704_14103.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___1704_14103.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___1704_14103.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___1704_14103.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___1704_14103.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___1704_14103.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___1704_14103.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___1704_14103.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___1704_14103.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___1704_14103.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___1704_14103.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___1704_14103.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___1704_14103.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___1704_14103.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___1704_14103.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___1704_14103.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___1704_14103.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___1704_14103.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___1704_14103.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___1704_14103.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___1704_14103.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___1704_14103.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___1704_14103.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___1704_14103.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___1704_14103.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___1704_14103.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___1704_14103.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___1704_14103.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___1704_14103.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___1704_14103.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___1704_14103.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___1704_14103.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___1704_14103.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___1704_14103.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___1704_14103.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___1704_14103.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___1704_14103.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___1704_14103.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___1704_14103.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___1704_14103.FStar_TypeChecker_Env.strict_args_tab)
                                    }) e
                                  in
                               FStar_All.pipe_right uu____14094
                                 (fun uu____14116  ->
                                    match uu____14116 with
                                    | (e1,uu____14124,uu____14125) -> e1)
                                in
                             FStar_All.pipe_right uu____14093
                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                  env')
                              in
                           FStar_All.pipe_right uu____14092 drop_lbtyp)
                       in
                    match uu____14083 with
                    | (e1,ms) ->
                        ((let uu____14131 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TwoPhases")
                             in
                          if uu____14131
                          then
                            let uu____14136 =
                              FStar_Syntax_Print.term_to_string e1  in
                            FStar_Util.print1
                              "Let binding after phase 1: %s\n" uu____14136
                          else ());
                         (let uu____14142 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TCDeclTime")
                             in
                          if uu____14142
                          then
                            let uu____14147 = FStar_Util.string_of_int ms  in
                            FStar_Util.print1
                              "Let binding elaborated (phase 1) in %s milliseconds\n"
                              uu____14147
                          else ());
                         e1)
                  else e  in
                let uu____14154 =
                  let uu____14163 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____14163 with
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
                (match uu____14154 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___1734_14268 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___1734_14268.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1734_14268.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1734_14268.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1734_14268.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___1741_14281 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1741_14281.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1741_14281.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___1741_14281.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___1741_14281.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1741_14281.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1741_14281.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____14282 =
                       FStar_Util.record_time
                         (fun uu____14301  ->
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              env' e1)
                        in
                     (match uu____14282 with
                      | (r1,ms) ->
                          ((let uu____14329 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TCDeclTime")
                               in
                            if uu____14329
                            then
                              let uu____14334 = FStar_Util.string_of_int ms
                                 in
                              FStar_Util.print1
                                "Let binding typechecked in phase 2 in %s milliseconds\n"
                                uu____14334
                            else ());
                           (let uu____14339 =
                              match r1 with
                              | ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                                   FStar_Syntax_Syntax.pos = uu____14364;
                                   FStar_Syntax_Syntax.vars = uu____14365;_},uu____14366,g)
                                  when FStar_TypeChecker_Env.is_trivial g ->
                                  let lbs2 =
                                    let uu____14396 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.snd lbs1)
                                        (FStar_List.map rename_parameters)
                                       in
                                    ((FStar_Pervasives_Native.fst lbs1),
                                      uu____14396)
                                     in
                                  let lbs3 =
                                    let uu____14420 =
                                      match post_tau with
                                      | FStar_Pervasives_Native.Some tau ->
                                          FStar_List.map (postprocess_lb tau)
                                            (FStar_Pervasives_Native.snd lbs2)
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.snd lbs2
                                       in
                                    ((FStar_Pervasives_Native.fst lbs2),
                                      uu____14420)
                                     in
                                  let quals1 =
                                    match e2.FStar_Syntax_Syntax.n with
                                    | FStar_Syntax_Syntax.Tm_meta
                                        (uu____14443,FStar_Syntax_Syntax.Meta_desugared
                                         (FStar_Syntax_Syntax.Masked_effect
                                         ))
                                        ->
                                        FStar_Syntax_Syntax.HasMaskedEffect
                                        :: quals
                                    | uu____14448 -> quals  in
                                  ((let uu___1771_14457 = se1  in
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_let
                                           (lbs3, lids));
                                      FStar_Syntax_Syntax.sigrng =
                                        (uu___1771_14457.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals = quals1;
                                      FStar_Syntax_Syntax.sigmeta =
                                        (uu___1771_14457.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (uu___1771_14457.FStar_Syntax_Syntax.sigattrs)
                                    }), lbs3)
                              | uu____14460 ->
                                  failwith
                                    "impossible (typechecking should preserve Tm_let)"
                               in
                            match uu____14339 with
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
                                 (let uu____14516 = log env1  in
                                  if uu____14516
                                  then
                                    let uu____14519 =
                                      let uu____14521 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.snd lbs1)
                                          (FStar_List.map
                                             (fun lb  ->
                                                let should_log =
                                                  let uu____14541 =
                                                    let uu____14550 =
                                                      let uu____14551 =
                                                        let uu____14554 =
                                                          FStar_Util.right
                                                            lb.FStar_Syntax_Syntax.lbname
                                                           in
                                                        uu____14554.FStar_Syntax_Syntax.fv_name
                                                         in
                                                      uu____14551.FStar_Syntax_Syntax.v
                                                       in
                                                    FStar_TypeChecker_Env.try_lookup_val_decl
                                                      env1 uu____14550
                                                     in
                                                  match uu____14541 with
                                                  | FStar_Pervasives_Native.None
                                                       -> true
                                                  | uu____14563 -> false  in
                                                if should_log
                                                then
                                                  let uu____14575 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  let uu____14577 =
                                                    FStar_Syntax_Print.term_to_string
                                                      lb.FStar_Syntax_Syntax.lbtyp
                                                     in
                                                  FStar_Util.format2
                                                    "let %s : %s" uu____14575
                                                    uu____14577
                                                else ""))
                                         in
                                      FStar_All.pipe_right uu____14521
                                        (FStar_String.concat "\n")
                                       in
                                    FStar_Util.print1 "%s\n" uu____14519
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
      (let uu____14629 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____14629
       then
         let uu____14632 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____14632
       else ());
      (let uu____14637 = get_fail_se se  in
       match uu____14637 with
       | FStar_Pervasives_Native.Some (uu____14658,false ) when
           let uu____14675 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____14675 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___1802_14701 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___1802_14701.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___1802_14701.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___1802_14701.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___1802_14701.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___1802_14701.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___1802_14701.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___1802_14701.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___1802_14701.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___1802_14701.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___1802_14701.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___1802_14701.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___1802_14701.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___1802_14701.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___1802_14701.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___1802_14701.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___1802_14701.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___1802_14701.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___1802_14701.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___1802_14701.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___1802_14701.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___1802_14701.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___1802_14701.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___1802_14701.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___1802_14701.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___1802_14701.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___1802_14701.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___1802_14701.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___1802_14701.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___1802_14701.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___1802_14701.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___1802_14701.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___1802_14701.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___1802_14701.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___1802_14701.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___1802_14701.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___1802_14701.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___1802_14701.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___1802_14701.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___1802_14701.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___1802_14701.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___1802_14701.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___1802_14701.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___1802_14701.FStar_TypeChecker_Env.strict_args_tab)
               }
             else env1  in
           ((let uu____14706 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____14706
             then
               let uu____14709 =
                 let uu____14711 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____14711
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____14709
             else ());
            (let uu____14725 =
               FStar_Errors.catch_errors
                 (fun uu____14755  ->
                    FStar_Options.with_saved_options
                      (fun uu____14767  -> tc_decl' env' se))
                in
             match uu____14725 with
             | (errs,uu____14779) ->
                 ((let uu____14809 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____14809
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____14844 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____14844  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____14856 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____14867 =
                            let uu____14877 = check_multi_eq errnos1 actual
                               in
                            match uu____14877 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- Prims.int_one), (~- Prims.int_one),
                                  (~- Prims.int_one))
                             in
                          (match uu____14867 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____14942 =
                                   let uu____14948 =
                                     let uu____14950 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____14953 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____14956 =
                                       FStar_Util.string_of_int e  in
                                     let uu____14958 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____14960 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____14950 uu____14953 uu____14956
                                       uu____14958 uu____14960
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____14948)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____14942)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____14987 .
    'Auu____14987 ->
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
               (fun uu___3_15030  ->
                  match uu___3_15030 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____15033 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____15044) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____15052 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____15062 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____15067 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____15083 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____15109 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15135) ->
            let uu____15144 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____15144
            then
              let for_export_bundle se1 uu____15181 =
                match uu____15181 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____15220,uu____15221) ->
                         let dec =
                           let uu___1878_15231 = se1  in
                           let uu____15232 =
                             let uu____15233 =
                               let uu____15240 =
                                 let uu____15241 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____15241  in
                               (l, us, uu____15240)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____15233
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____15232;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1878_15231.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1878_15231.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1878_15231.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____15251,uu____15252,uu____15253) ->
                         let dec =
                           let uu___1889_15261 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1889_15261.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1889_15261.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1889_15261.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____15266 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____15289,uu____15290,uu____15291) ->
            let uu____15292 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____15292 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____15316 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____15316
            then
              ([(let uu___1905_15335 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___1905_15335.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___1905_15335.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___1905_15335.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____15338 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_15344  ->
                         match uu___4_15344 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____15347 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____15353 ->
                             true
                         | uu____15355 -> false))
                  in
               if uu____15338 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____15376 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____15381 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15386 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____15391 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15396 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____15414) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____15428 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____15428
            then ([], hidden)
            else
              (let dec =
                 let uu____15449 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____15449;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____15460 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____15460
            then
              let uu____15471 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1942_15485 = se  in
                        let uu____15486 =
                          let uu____15487 =
                            let uu____15494 =
                              let uu____15495 =
                                let uu____15498 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____15498.FStar_Syntax_Syntax.fv_name  in
                              uu____15495.FStar_Syntax_Syntax.v  in
                            (uu____15494, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____15487  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____15486;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1942_15485.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1942_15485.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1942_15485.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____15471, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____15521 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____15521
       then
         let uu____15524 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____15524
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____15529 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____15547 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
           uu____15564) ->
           let env1 =
             let uu___1963_15569 = env  in
             let uu____15570 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1963_15569.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1963_15569.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1963_15569.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1963_15569.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1963_15569.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1963_15569.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1963_15569.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1963_15569.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1963_15569.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1963_15569.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1963_15569.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1963_15569.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1963_15569.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1963_15569.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1963_15569.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1963_15569.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1963_15569.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1963_15569.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1963_15569.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1963_15569.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1963_15569.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1963_15569.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1963_15569.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1963_15569.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1963_15569.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1963_15569.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1963_15569.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1963_15569.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1963_15569.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1963_15569.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1963_15569.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1963_15569.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1963_15569.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1963_15569.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____15570;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1963_15569.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1963_15569.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1963_15569.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1963_15569.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1963_15569.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1963_15569.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1963_15569.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1963_15569.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1963_15569.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
           let env1 =
             let uu___1963_15572 = env  in
             let uu____15573 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1963_15572.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1963_15572.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1963_15572.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1963_15572.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1963_15572.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1963_15572.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1963_15572.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1963_15572.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1963_15572.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1963_15572.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1963_15572.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1963_15572.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1963_15572.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1963_15572.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1963_15572.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1963_15572.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1963_15572.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1963_15572.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1963_15572.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1963_15572.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1963_15572.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1963_15572.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1963_15572.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1963_15572.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1963_15572.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1963_15572.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1963_15572.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1963_15572.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1963_15572.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1963_15572.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1963_15572.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1963_15572.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1963_15572.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1963_15572.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____15573;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1963_15572.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1963_15572.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1963_15572.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1963_15572.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1963_15572.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1963_15572.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1963_15572.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1963_15572.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1963_15572.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions
           uu____15574) ->
           let env1 =
             let uu___1963_15577 = env  in
             let uu____15578 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1963_15577.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1963_15577.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1963_15577.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1963_15577.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1963_15577.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1963_15577.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1963_15577.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1963_15577.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1963_15577.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1963_15577.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1963_15577.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1963_15577.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1963_15577.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1963_15577.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1963_15577.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1963_15577.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1963_15577.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1963_15577.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1963_15577.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1963_15577.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1963_15577.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1963_15577.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1963_15577.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1963_15577.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1963_15577.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1963_15577.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1963_15577.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1963_15577.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1963_15577.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1963_15577.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1963_15577.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1963_15577.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1963_15577.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1963_15577.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____15578;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1963_15577.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1963_15577.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1963_15577.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1963_15577.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1963_15577.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1963_15577.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1963_15577.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1963_15577.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1963_15577.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____15579) ->
           let env1 =
             let uu___1963_15584 = env  in
             let uu____15585 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1963_15584.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1963_15584.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1963_15584.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1963_15584.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1963_15584.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1963_15584.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1963_15584.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1963_15584.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1963_15584.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1963_15584.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1963_15584.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1963_15584.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1963_15584.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1963_15584.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1963_15584.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1963_15584.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1963_15584.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1963_15584.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1963_15584.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1963_15584.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1963_15584.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1963_15584.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1963_15584.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1963_15584.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1963_15584.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1963_15584.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1963_15584.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1963_15584.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1963_15584.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1963_15584.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1963_15584.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1963_15584.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1963_15584.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1963_15584.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____15585;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1963_15584.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1963_15584.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1963_15584.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1963_15584.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1963_15584.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1963_15584.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1963_15584.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1963_15584.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1963_15584.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver )
           ->
           ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
              ();
            env)
       | FStar_Syntax_Syntax.Sig_pragma uu____15587 -> env
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15588 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____15598 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____15598) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____15599,uu____15600,uu____15601) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_15606  ->
                   match uu___5_15606 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____15609 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____15611,uu____15612) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_15621  ->
                   match uu___5_15621 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____15624 -> false))
           -> env
       | uu____15626 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____15695 se =
        match uu____15695 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____15748 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____15748
              then
                let uu____15751 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____15751
              else ());
             (let uu____15756 = tc_decl env1 se  in
              match uu____15756 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____15809 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____15809
                             then
                               let uu____15813 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____15813
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____15829 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____15829
                             then
                               let uu____15833 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____15833
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
                    (let uu____15850 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____15850
                     then
                       let uu____15855 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____15864 =
                                  let uu____15866 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____15866 "\n"  in
                                Prims.op_Hat s uu____15864) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____15855
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____15876 =
                       let uu____15885 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____15885
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____15927 se1 =
                            match uu____15927 with
                            | (exports1,hidden1) ->
                                let uu____15955 = for_export env3 hidden1 se1
                                   in
                                (match uu____15955 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____15876 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____16109 = acc  in
        match uu____16109 with
        | (uu____16144,uu____16145,env1,uu____16147) ->
            let uu____16160 =
              FStar_Util.record_time
                (fun uu____16207  -> process_one_decl acc se)
               in
            (match uu____16160 with
             | (r,ms_elapsed) ->
                 ((let uu____16273 =
                     ((FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TCDeclTime"))
                        ||
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.attr_eq
                              FStar_Syntax_Util.tcdecltime_attr)
                           se.FStar_Syntax_Syntax.sigattrs))
                       || (FStar_Options.timing ())
                      in
                   if uu____16273
                   then
                     let uu____16277 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____16279 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____16277 uu____16279
                   else ());
                  r))
         in
      let uu____16284 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____16284 with
      | (ses1,exports,env1,uu____16332) ->
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
          let uu___2060_16370 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2060_16370.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2060_16370.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2060_16370.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2060_16370.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2060_16370.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2060_16370.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2060_16370.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2060_16370.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2060_16370.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2060_16370.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___2060_16370.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___2060_16370.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___2060_16370.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2060_16370.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2060_16370.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___2060_16370.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2060_16370.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___2060_16370.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2060_16370.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___2060_16370.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___2060_16370.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___2060_16370.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2060_16370.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2060_16370.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2060_16370.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2060_16370.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2060_16370.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2060_16370.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2060_16370.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2060_16370.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2060_16370.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2060_16370.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2060_16370.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2060_16370.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___2060_16370.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2060_16370.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2060_16370.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2060_16370.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2060_16370.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2060_16370.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2060_16370.FStar_TypeChecker_Env.strict_args_tab)
          }  in
        let check_term lid univs1 t =
          let uu____16390 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____16390 with
          | (univs2,t1) ->
              ((let uu____16398 =
                  let uu____16400 =
                    let uu____16406 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____16406  in
                  FStar_All.pipe_left uu____16400
                    (FStar_Options.Other "Exports")
                   in
                if uu____16398
                then
                  let uu____16410 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____16412 =
                    let uu____16414 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____16414
                      (FStar_String.concat ", ")
                     in
                  let uu____16431 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____16410 uu____16412 uu____16431
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____16437 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____16437 (fun a2  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____16463 =
             let uu____16465 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____16467 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____16465 uu____16467
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____16463);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16478) ->
              let uu____16487 =
                let uu____16489 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____16489  in
              if uu____16487
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____16503,uu____16504) ->
              let t =
                let uu____16516 =
                  let uu____16523 =
                    let uu____16524 =
                      let uu____16539 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____16539)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____16524  in
                  FStar_Syntax_Syntax.mk uu____16523  in
                uu____16516 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____16555,uu____16556,uu____16557) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____16567 =
                let uu____16569 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____16569  in
              if uu____16567 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____16577,lbs),uu____16579) ->
              let uu____16590 =
                let uu____16592 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____16592  in
              if uu____16590
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
              let uu____16615 =
                let uu____16617 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____16617  in
              if uu____16615
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____16638 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____16639 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____16646 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____16647 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____16648 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____16649 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____16656 -> ()  in
        let uu____16657 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____16657 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____16763) -> true
             | uu____16765 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____16795 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____16834 ->
                   let uu____16835 =
                     let uu____16842 =
                       let uu____16843 =
                         let uu____16858 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____16858)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____16843  in
                     FStar_Syntax_Syntax.mk uu____16842  in
                   uu____16835 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____16875,uu____16876) ->
            let s1 =
              let uu___2186_16886 = s  in
              let uu____16887 =
                let uu____16888 =
                  let uu____16895 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____16895)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____16888  in
              let uu____16896 =
                let uu____16899 =
                  let uu____16902 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____16902  in
                FStar_Syntax_Syntax.Assumption :: uu____16899  in
              {
                FStar_Syntax_Syntax.sigel = uu____16887;
                FStar_Syntax_Syntax.sigrng =
                  (uu___2186_16886.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____16896;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2186_16886.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___2186_16886.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____16905 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____16930 lbdef =
        match uu____16930 with
        | (uvs,t) ->
            let attrs =
              let uu____16941 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____16941
              then
                let uu____16946 =
                  let uu____16947 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____16947
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____16946 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___2199_16950 = s  in
            let uu____16951 =
              let uu____16954 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____16954  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___2199_16950.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____16951;
              FStar_Syntax_Syntax.sigmeta =
                (uu___2199_16950.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____16972 -> failwith "Impossible!"  in
        let c_opt =
          let uu____16979 = FStar_Syntax_Util.is_unit t  in
          if uu____16979
          then
            let uu____16986 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____16986
          else
            (let uu____16993 =
               let uu____16994 = FStar_Syntax_Subst.compress t  in
               uu____16994.FStar_Syntax_Syntax.n  in
             match uu____16993 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____17001,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____17025 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____17037 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____17037
            then false
            else
              (let uu____17044 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____17044
               then true
               else
                 (let uu____17051 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____17051))
         in
      let extract_sigelt s =
        (let uu____17063 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____17063
         then
           let uu____17066 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____17066
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____17073 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____17093 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____17112 ->
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
                             (lid,uu____17158,uu____17159,uu____17160,uu____17161,uu____17162)
                             ->
                             ((let uu____17172 =
                                 let uu____17175 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____17175  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____17172);
                              (let uu____17224 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____17224 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____17228,uu____17229,uu____17230,uu____17231,uu____17232)
                             ->
                             ((let uu____17240 =
                                 let uu____17243 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____17243  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____17240);
                              sigelts1)
                         | uu____17292 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____17301 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____17301
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____17311 =
                    let uu___2263_17312 = s  in
                    let uu____17313 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2263_17312.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2263_17312.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____17313;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2263_17312.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2263_17312.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____17311])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____17324 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____17324
             then []
             else
               (let uu____17331 = lbs  in
                match uu____17331 with
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
                        (fun uu____17393  ->
                           match uu____17393 with
                           | (uu____17401,t,uu____17403) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____17420  ->
                             match uu____17420 with
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
                           (fun uu____17447  ->
                              match uu____17447 with
                              | (uu____17455,t,uu____17457) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____17469,uu____17470) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____17478 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____17507 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____17507) uu____17478
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____17511 =
                    let uu___2305_17512 = s  in
                    let uu____17513 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2305_17512.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2305_17512.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____17513;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2305_17512.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2305_17512.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____17511]
                else [])
             else
               (let uu____17520 =
                  let uu___2307_17521 = s  in
                  let uu____17522 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___2307_17521.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___2307_17521.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____17522;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___2307_17521.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___2307_17521.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____17520])
         | FStar_Syntax_Syntax.Sig_new_effect uu____17525 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____17526 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____17527 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____17528 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____17541 -> [s])
         in
      let uu___2319_17542 = m  in
      let uu____17543 =
        let uu____17544 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____17544 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___2319_17542.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____17543;
        FStar_Syntax_Syntax.exports =
          (uu___2319_17542.FStar_Syntax_Syntax.exports);
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
        (fun uu____17595  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____17642  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____17657 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____17657
  
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
      (let uu____17746 = FStar_Options.debug_any ()  in
       if uu____17746
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
         let uu___2344_17762 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___2344_17762.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___2344_17762.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___2344_17762.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___2344_17762.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___2344_17762.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___2344_17762.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___2344_17762.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___2344_17762.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___2344_17762.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___2344_17762.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___2344_17762.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___2344_17762.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___2344_17762.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___2344_17762.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___2344_17762.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___2344_17762.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___2344_17762.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___2344_17762.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___2344_17762.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___2344_17762.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___2344_17762.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___2344_17762.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___2344_17762.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___2344_17762.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___2344_17762.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___2344_17762.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___2344_17762.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___2344_17762.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___2344_17762.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___2344_17762.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___2344_17762.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___2344_17762.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___2344_17762.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___2344_17762.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___2344_17762.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___2344_17762.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___2344_17762.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___2344_17762.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___2344_17762.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___2344_17762.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___2344_17762.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___2344_17762.FStar_TypeChecker_Env.strict_args_tab)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____17764 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____17764 with
       | (ses,exports,env3) ->
           ((let uu___2352_17797 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___2352_17797.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___2352_17797.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___2352_17797.FStar_Syntax_Syntax.is_interface)
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
        let uu____17826 = tc_decls env decls  in
        match uu____17826 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___2361_17857 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___2361_17857.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___2361_17857.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___2361_17857.FStar_Syntax_Syntax.is_interface)
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
        let uu____17918 = tc_partial_modul env01 m  in
        match uu____17918 with
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
                (let uu____17955 = FStar_Errors.get_err_count ()  in
                 uu____17955 = Prims.int_zero)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____17966 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____17966
                then
                  let uu____17970 =
                    let uu____17972 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____17972 then "" else " (in lax mode) "  in
                  let uu____17980 =
                    let uu____17982 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____17982
                    then
                      let uu____17986 =
                        let uu____17988 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.op_Hat uu____17988 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____17986
                    else ""  in
                  let uu____17995 =
                    let uu____17997 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____17997
                    then
                      let uu____18001 =
                        let uu____18003 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____18003 "\n"  in
                      Prims.op_Hat "\nto: " uu____18001
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____17970
                    uu____17980 uu____17995
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___2387_18017 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2387_18017.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2387_18017.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2387_18017.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2387_18017.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2387_18017.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2387_18017.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2387_18017.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2387_18017.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2387_18017.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2387_18017.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2387_18017.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2387_18017.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2387_18017.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2387_18017.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2387_18017.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2387_18017.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2387_18017.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2387_18017.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2387_18017.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2387_18017.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2387_18017.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2387_18017.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2387_18017.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2387_18017.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2387_18017.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2387_18017.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2387_18017.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2387_18017.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2387_18017.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2387_18017.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2387_18017.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___2387_18017.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2387_18017.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2387_18017.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2387_18017.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2387_18017.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2387_18017.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2387_18017.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2387_18017.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2387_18017.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2387_18017.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2387_18017.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2387_18017.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let en02 =
                    let uu___2390_18019 = en01  in
                    let uu____18020 =
                      let uu____18035 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____18035, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2390_18019.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2390_18019.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2390_18019.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2390_18019.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2390_18019.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2390_18019.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2390_18019.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2390_18019.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2390_18019.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2390_18019.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2390_18019.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2390_18019.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2390_18019.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2390_18019.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2390_18019.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2390_18019.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2390_18019.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2390_18019.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2390_18019.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2390_18019.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2390_18019.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2390_18019.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2390_18019.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2390_18019.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2390_18019.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2390_18019.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2390_18019.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2390_18019.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2390_18019.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2390_18019.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2390_18019.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____18020;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2390_18019.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2390_18019.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2390_18019.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2390_18019.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2390_18019.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2390_18019.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2390_18019.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2390_18019.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2390_18019.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___2390_18019.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2390_18019.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2390_18019.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let uu____18081 =
                    let uu____18083 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____18083  in
                  if uu____18081
                  then
                    ((let uu____18087 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____18087 (fun a3  -> ()));
                     en02)
                  else en02  in
                let uu____18091 = tc_modul en0 modul_iface true  in
                match uu____18091 with
                | (modul_iface1,env) ->
                    ((let uu___2399_18104 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___2399_18104.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___2399_18104.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___2399_18104.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___2401_18108 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___2401_18108.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___2401_18108.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___2401_18108.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____18111 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____18111 FStar_Util.smap_clear);
               (let uu____18147 =
                  ((let uu____18151 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____18151) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____18154 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____18154)
                   in
                if uu____18147 then check_exports env modul exports else ());
               (let uu____18160 =
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____18160 (fun a4  -> ()));
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
        let uu____18175 =
          let uu____18177 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____18177  in
        push_context env uu____18175  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____18198 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____18209 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____18209 with | (uu____18216,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____18241 = FStar_Options.debug_any ()  in
         if uu____18241
         then
           let uu____18244 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____18244
         else ());
        (let uu____18256 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____18256
         then
           let uu____18259 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____18259
         else ());
        (let env1 =
           let uu___2431_18265 = env  in
           let uu____18266 =
             let uu____18268 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____18268  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___2431_18265.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___2431_18265.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___2431_18265.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___2431_18265.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___2431_18265.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___2431_18265.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___2431_18265.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___2431_18265.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___2431_18265.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___2431_18265.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___2431_18265.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___2431_18265.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___2431_18265.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___2431_18265.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___2431_18265.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___2431_18265.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___2431_18265.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___2431_18265.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___2431_18265.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___2431_18265.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____18266;
             FStar_TypeChecker_Env.lax_universes =
               (uu___2431_18265.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___2431_18265.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___2431_18265.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___2431_18265.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___2431_18265.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___2431_18265.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___2431_18265.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___2431_18265.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___2431_18265.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___2431_18265.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___2431_18265.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___2431_18265.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___2431_18265.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___2431_18265.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___2431_18265.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___2431_18265.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___2431_18265.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___2431_18265.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___2431_18265.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___2431_18265.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___2431_18265.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___2431_18265.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___2431_18265.FStar_TypeChecker_Env.strict_args_tab)
           }  in
         let uu____18270 = tc_modul env1 m b  in
         match uu____18270 with
         | (m1,env2) ->
             ((let uu____18282 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____18282
               then
                 let uu____18285 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____18285
               else ());
              (let uu____18291 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____18291
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
                         let uu____18329 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____18329 with
                         | (univnames1,e) ->
                             let uu___2453_18336 = lb  in
                             let uu____18337 =
                               let uu____18340 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____18340 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2453_18336.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2453_18336.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___2453_18336.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2453_18336.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____18337;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2453_18336.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2453_18336.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___2455_18341 = se  in
                       let uu____18342 =
                         let uu____18343 =
                           let uu____18350 =
                             let uu____18351 = FStar_List.map update lbs  in
                             (b1, uu____18351)  in
                           (uu____18350, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____18343  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____18342;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___2455_18341.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___2455_18341.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___2455_18341.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___2455_18341.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____18359 -> se  in
                 let normalized_module =
                   let uu___2459_18361 = m1  in
                   let uu____18362 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___2459_18361.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____18362;
                     FStar_Syntax_Syntax.exports =
                       (uu___2459_18361.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___2459_18361.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____18363 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____18363
               else ());
              (m1, env2)))
  